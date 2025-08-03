use clap::Parser;
use serde::Deserialize;
use std::{fs, path::PathBuf};

/// Simple CLI to convert a Solidity ABI JSON into a Lean contract stub.
#[derive(Parser)]
struct Cli {
    /// Path to ABI JSON file
    #[arg(short, long)]
    abi: PathBuf,

    /// Output Lean file path
    #[arg(short, long)]
    output: PathBuf,
}

#[derive(Deserialize)]
struct AbiEntry {
    #[serde(rename = "type")] ty: String,
    name: Option<String>,
}

fn main() -> anyhow::Result<()> {
    let args = Cli::parse();
    let abi_data = fs::read_to_string(&args.abi)?;
    let entries: Vec<AbiEntry> = serde_json::from_str(&abi_data)?;

    let functions: Vec<String> = entries
        .into_iter()
        .filter(|e| e.ty == "function")
        .filter_map(|e| e.name)
        .collect();

    let module_name = args
        .output
        .file_stem()
        .unwrap()
        .to_string_lossy()
        .to_string();

    let mut lean = String::new();
    lean.push_str(&format!("import Mathlib\nimport Internal.Core\n\nnamespace {}\n\n", module_name));
    lean.push_str("inductive Prim where\n");
    for fname in &functions {
        lean.push_str(&format!("  | {}\n", fname));
    }
    lean.push_str("  deriving Repr, DecidableEq\n\n");
    lean.push_str("abbrev Action := List Prim\n\n");
    lean.push_str("structure State where\n  dummy : Unit := ()\n\n@[simp]\ndef step : Action → State → State := by\n  intro _ σ; exact σ\n\nopen Contract\n\ndef spec : Spec := { State := State, Action := Action, step := step }\n\ninstance : HasId Action where\n  idAct := []\n\ninstance : HasComp Action where\n  compAct := List.append\n\ninstance : IsCategory spec := by\n  refine { id_left := ?_, id_right := ?_, assoc := ?_ } <;> intros <;> simp [step, List.append_assoc]\n\nend {}\n");
    lean.push_str("@[simp]\ndef compilePrim : Prim → EVM.OpCode := fun _ => EVM.OpCode.CALL\n\n");
    lean.push_str("@[simp]\ndef compile (act : Action) : EVM.Trace :=\n  let n := act.length\n  { ops    := List.repeat (EVM.OpCode.CALL) n,\n    gas    := n,\n    diff   := { updates := act.map (fun p => toString p) },\n    status := EVM.ExecStatus.success }\n\n");
    lean.push_str("open EVM\n\n");
    lean.push_str("lemma compile_id : compile (HasId.idAct : Action) = idTrace := by\n  simp [compile, HasId.idAct, idTrace]\n\n");
    lean.push_str("lemma compile_pres (a b : Action) :\n    comp (compile a) (compile b) = some (compile (List.append a b)) := by\n  simp [compile, comp, List.length_append, List.map_append, List.repeat_append]\n\n");

    fs::write(&args.output, lean)?;
    println!("Generated {}", args.output.display());
    Ok(())
} 