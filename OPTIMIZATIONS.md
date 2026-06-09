# Memory & Performance Optimizations — Constraint Simplification

Changes on the `circom-zisk-1.0.0` branch that cut peak memory and compile time of the
constraint-simplification phase **without changing the compiler's output** (the emitted
`.r1cs` stays byte-identical to the unoptimized compiler).

The target workload: large recursion/aggregation circuits with **tens of millions of
wiring equalities** (`s_i == s_j`), where simplification dominated peak RSS.

---

## The core idea in one picture

An equality `s_i == s_j` carries almost no information — just two signals and the relation
between their coefficients. But the old pipeline stored each one as a full `Constraint`:

```
        OLD: one Constraint per equality            NEW: one tuple per equality
     ┌─────────────────────────────────┐
     │ Constraint                       │
     │   a: HashMap<usize, BigInt>  ▒▒▒ │
     │   b: HashMap<usize, BigInt>  ▒▒▒ │           ( lo , hi , c_lo )
     │   c: HashMap<usize, BigInt>  ▒▒▒ │            usize usize BigInt
     │      → {s_i: c_i, s_j: -c_i}     │
     └─────────────────────────────────┘
        3 HashMaps + BigInts                         a few machine words
        ~hundreds of bytes                           + one BigInt
                  │                                           │
                  └───────────  × ~83,000,000  ───────────────┘
                         this difference is the whole optimization
```

`c_hi == -c_lo` over the field (the invariant `is_equality` checks), so a single stored
coefficient `c_lo` fully reconstructs the constraint when we ever need it back.

---

## Where equalities live in the pipeline

```
  DAG ──► map_tree ──► split constraints into buckets ──► simplify each bucket ──► .r1cs
          (dag/src/map_to_constraint_list.rs)

                          ┌──────────────────────────────┐
                          │  constant equalities (s == k) │
                          │  EQUALITIES      (s_i == s_j)  │ ◄── this work
                          │  linear                        │
                          │  non-linear                    │
                          └──────────────────────────────┘
```

For the equalities bucket, simplification (`constraint_list/src/constraint_simplification.rs`):

```
   equalities ──► build_eq_clusters ──► for each cluster: pick a representative,
   Vec<EqPair>    (union-find on             substitute the rest away
                   shared signals)           (s_other := s_rep)
```

A signal is **forbidden** when it sits on a custom-gate boundary (`pragma
custom_templates`) and must survive into the final witness — it can't be substituted away.

---

## What changed, with code references

### 1. Compact equality storage — `EqPair`

> [`constraint_list/src/lib.rs:19`](constraint_list/src/lib.rs#L19)

```rust
pub type EqPair = (usize, usize, circom_algebra::num_bigint::BigInt);
//                  lo     hi     c_lo  (and c_hi == -c_lo over the field)
```

`Simplifier.equalities` and `CHolder.equalities` change from `LinkedList<Constraint>` to
`Vec<EqPair>`.

The tuple is filled at map time:

> [`dag/src/map_to_constraint_list.rs:30-36`](dag/src/map_to_constraint_list.rs#L30-L36)

`take_cloned_signals_ordered` yields the two signals ascending (so `lo < hi`), and we grab
`lo`'s coefficient from the constraint before discarding it.

### 2. Clustering without `Constraint`s — `EqCluster` / `build_eq_clusters`

> [`constraint_list/src/constraint_simplification.rs:104-130`](constraint_list/src/constraint_simplification.rs#L104-L130) (`EqCluster`)
> [`constraint_list/src/constraint_simplification.rs:132-185`](constraint_list/src/constraint_simplification.rs#L132-L185) (`build_eq_clusters`)

`build_eq_clusters` is a line-for-line mirror of the existing `build_clusters`
(same arena + path-compressed union-find) but unions over `EqPair`s and never allocates a
`Constraint`. `EqCluster` holds a `LinkedList<EqPair>` so union-find merges are O(1)
splices (a `Vec` would copy on every merge → quadratic on huge clusters).

### 3. Substitutions as plain `(from, to)` pairs

> [`constraint_list/src/constraint_simplification.rs`](constraint_list/src/constraint_simplification.rs#L230) (`eq_cluster_simplification`)

Returns `Vec<SubPair>` where `SubPair = (from, to)` ("substitute `from := to`") instead of
`LinkedList<Substitution>`. The forbidden / non-forbidden branch logic is unchanged.

### 4. Rebuilding the exact constraint when an equality must be kept

> [`constraint_list/src/constraint_simplification.rs:221`](constraint_list/src/constraint_simplification.rs#L221) (`equality_constraint`)

When **both** signals are forbidden, the equality is kept as a real constraint. We
reconstruct `{s_a: c_a, s_b: -c_a}` from the stored coefficient — the *exact* original, not
a canonical `+1/-1` form (this is the correctness fix, below). Field-agnostic via
`modular_arithmetic`.

### 5. Signal→signal substitution (no heavy expressions)

> [`circom_algebra/src/simplification_utils.rs:512`](circom_algebra/src/simplification_utils.rs#L512) (`fast_signal_constraint_substitution`)

Equality substitutions are always `signal → signal`. This is a specialization of
`fast_encoded_constraint_substitution` whose map stores a bare `usize` instead of an
`ArithmeticExpression` — behaviourally identical, ~10× smaller, clones nothing.

### 6. Build the heavy substitution map only for *relevant* signals

> [`constraint_list/src/constraint_simplification.rs`](constraint_list/src/constraint_simplification.rs#L582) (the `single_substitutions` block)

```
   all equality subs ──► compact signal→usize map ──► apply to linear / cons_equalities
   (Vec<SubPair>)        (record every `from` in `deleted`)        + drop it
                              │
                              └─► build the heavy HashMap<usize, A> ONLY for subs whose
                                  `from` is referenced by a non-linear constraint
                                  (almost all are discarded → ~83M expressions never built)
```

Replaces the old "build the full encoded map, then prune" flow.

### 7. Infrastructure (no effect on output)

| Change | Where |
|--------|-------|
| `mimalloc` global allocator | [`circom/src/main.rs:7-8`](circom/src/main.rs#L7-L8), [`circom/Cargo.toml:27`](circom/Cargo.toml#L27) |
| `codegen-units = 1` (release) | [`Cargo.toml:17-18`](Cargo.toml#L17-L18) |
| `mimalloc`/`libmimalloc-sys` deps, `cc`/`shlex` bumps | `Cargo.lock` |

---

## The correctness subtlety (why `EqPair` carries a coefficient)

A bare `(lo, hi)` pair was tempting — but it loses the coefficients, and the
forbidden-forbidden path *keeps* the constraint. Re-emitting it in a canonical `+1/-1`
form is algebraically equivalent but **not byte-identical**: `is_equality` accepts any
`(k, -k)`, so the circuit's original sign/magnitude can differ.

```
   original kept constraint:  { s_a:  +1 , s_b: -1 }   (or 2/-2, or -1/+1, …)
   canonical rebuild:         { s_a:  -1 , s_b: +1 }   ← sign flipped → different bytes
                                     ▲
                          on Keccak this flipped 342,360 coefficient
                          bytes (+1 ↔ p-1) → golden md5 mismatch
```

So `EqPair` keeps `c_lo`, and `equality_constraint` rebuilds the original exactly.

**Why capture it unconditionally** (not just for forbidden pairs)? `map_tree` fills the
`forbidden` set *as it recurses*:

```
            map_tree(node)
              ├─ mark node's custom-gate signals forbidden
              ├─ classify this node's equalities   ◄── forbidden set is INCOMPLETE here:
              │                                        a signal forbidden by a LATER
              └─ recurse into children ───────────►    sibling/subtree isn't in it yet
```

At classification time you can't yet know whether an equality will hit the
forbidden-forbidden path, so deciding "keep coefficient only if forbidden" would
mis-store. Capturing `c_lo` for every equality is the single-pass, always-correct choice.

> The multi-signal cluster path still canonicalizes via `A::sub` — but that already matched
> the pre-optimization compiler, so it is unchanged.

---

## Validation

Verified byte-identical (`.r1cs` md5) against the unoptimized compiler across all zisk
circuits, both prime fields (goldilocks + bn128), including every `pragma custom_templates`
circuit (which exercises the forbidden-forbidden path).
