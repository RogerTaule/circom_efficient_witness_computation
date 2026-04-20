use super::ir_interface::*;
use crate::translating_traits::*;
use code_producers::c_elements::*;
use code_producers::wasm_elements::*;

#[derive(Clone)]
pub struct LoopBucket {
    pub line: usize,
    pub message_id: usize,
    pub continue_condition: InstructionPointer,
    pub body: InstructionList,
}

impl IntoInstruction for LoopBucket {
    fn into_instruction(self) -> Instruction {
        Instruction::Loop(self)
    }
}

impl Allocate for LoopBucket {
    fn allocate(self) -> InstructionPointer {
        InstructionPointer::new(self.into_instruction())
    }
}

impl ObtainMeta for LoopBucket {
    fn get_line(&self) -> usize {
        self.line
    }
    fn get_message_id(&self) -> usize {
        self.message_id
    }
}

impl ToString for LoopBucket {
    fn to_string(&self) -> String {
        let line = self.line.to_string();
        let template_id = self.message_id.to_string();
        let cond = self.continue_condition.to_string();
        let mut body = "".to_string();
        for i in &self.body {
            body = format!("{}{};", body, i.to_string());
        }
        format!("LOOP(line:{},template_id:{},cond:{},body:{})", line, template_id, cond, body)
    }
}

impl WriteWasm for LoopBucket {
    fn produce_wasm(&self, producer: &WASMProducer) -> Vec<String> {
        use code_producers::wasm_elements::wasm_code_generator::*;
        let mut instructions = vec![];
        if producer.needs_comments() {
            instructions.push(format!(";; loop bucket. Line {}", self.line)); //.to_string()
	}
        instructions.push(add_block());
        instructions.push(add_loop());
        let mut instructions_continue = self.continue_condition.produce_wasm(producer);
        instructions.append(&mut instructions_continue);
        instructions.push(call("$Fr_isTrue"));
        instructions.push(eqz32());
        instructions.push(br_if("1"));
        for ins in &self.body {
            let mut instructions_loop = ins.produce_wasm(producer);
            instructions.append(&mut instructions_loop);
        }
        instructions.push(br("0"));
        instructions.push(add_end());
        instructions.push(add_end());
        if producer.needs_comments() {
            instructions.push(";; end of loop bucket".to_string());
	}
        instructions
    }
}

fn try_detect_induction_loop(continue_result: &str) -> Option<(String, String)> {
    let prefix = "Fr_lt(lvar[";
    if !continue_result.starts_with(prefix) {
        return None;
    }
    let after_prefix = &continue_result[prefix.len()..];
    let close_bracket = after_prefix.find(']')?;
    let n_str = &after_prefix[..close_bracket];
    if !n_str.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    let after_bracket = &after_prefix[close_bracket + 1..];
    if !after_bracket.starts_with(',') {
        return None;
    }
    let after_comma = &after_bracket[1..];
    if !after_comma.ends_with("ull)") {
        return None;
    }
    let k_str = &after_comma[..after_comma.len() - 4];
    if !k_str.chars().all(|c| c.is_ascii_digit()) {
        return None;
    }
    Some((n_str.to_string(), k_str.to_string()))
}

impl WriteC for LoopBucket {
    fn produce_c(&self, producer: &CProducer, parallel: Option<bool>) -> (Vec<String>, String) {
        use c_code_generator::merge_code;
        let (continue_code, raw_continue_result) = self.continue_condition.produce_c(producer, parallel);

        let mut body = vec![];
        for instr in &self.body {
            let (mut instr_code, _) = instr.produce_c(producer, parallel);
            body.append(&mut instr_code);
        }

        if producer.prime_str == "goldilocks" && continue_code.is_empty() {
            if let Some((n, k)) = try_detect_induction_loop(&raw_continue_result) {
                // Safety: K must be a small positive integer so that native u64 `<`
                // matches Fr_lt semantics (both values are below Fr_half = 2^63).
                let k_val: u64 = k.parse().unwrap_or(u64::MAX);
                let fr_half: u64 = (1u64 << 63) - 1;
                let increment_pattern = format!("lvar[{}] = Fr_add(lvar[{}],1ull);", n, n);
                // Only optimize if: bound is small AND the unit-step increment is present
                // exactly once in the body (guards against step!=1 or missing increment).
                let increment_count = body.iter()
                    .filter(|line| line.trim() == increment_pattern.as_str())
                    .count();
                if k_val <= fr_half && increment_count == 1 {
                    let fr_toint_pattern = format!("Fr_toInt(lvar[{}])", n);
                    let fr_toint_replacement = format!("(uint)lvar[{}]", n);
                    let optimized_body: Vec<String> = body.into_iter()
                        .filter(|line| line.trim() != increment_pattern.as_str())
                        .map(|line| line.replace(&fr_toint_pattern, &fr_toint_replacement))
                        .collect();
                    let while_loop = format!(
                        "while(lvar[{}] < {}){{\n{}lvar[{}]++;\n}}",
                        n, k, merge_code(optimized_body), n
                    );
                    return (vec![while_loop], "".to_string());
                }
            }
        }

        let continue_result = format!("Fr_isTrue({})", raw_continue_result);
        body.append(&mut continue_code.clone());
        let while_loop = format!("while({}){{\n{}}}", continue_result, merge_code(body));
        let mut loop_c = continue_code;
        loop_c.push(while_loop);
        (loop_c, "".to_string())
    }
}
