/--
Bridge type recording delay δ and natural transformation between chain
presheaves.  Concrete bridges (HTLB, zk, sig) will inhabit this record.
-/

import Time.Category
import Stack.Global
import Bridge.Natural
import Chain
import Mathlib.CategoryTheory.Functor
import Mathlib.CategoryTheory.NatTrans

/-!
Enhanced bridge types with cryptographic proof objects.
-/

namespace Bridge

/-- Proof types for different bridge mechanisms. -/
inductive ProofType
  | htlb (hash : String) (timeout : ℕ)
  | zkSnark (proof : String) (publicInputs : List String)
  | thresholdSig (signatures : List String) (threshold : ℕ)
  deriving Repr

/-- Enhanced bridge structure with proof object. -/
structure Bridge where
  source : Chain
  target : Chain  
  δ : ℕ  -- delay in blocks
  proof : ProofType
  nt : NT  -- the natural transformation

/-- A bridge is valid if it has the required proof components. -/
def Bridge.isValid (b : Bridge) : Prop :=
  match b.proof with
  | .htlb _ timeout => timeout > b.δ  -- timeout must exceed delay
  | .zkSnark _ inputs => inputs.length > 0  -- must have public inputs
  | .thresholdSig sigs t => sigs.length ≥ t  -- enough signatures

/-- HTLB bridge constructor. -/
def htlbBridge (source target : Chain) (δ : ℕ) (hash : String) (timeout : ℕ) : Bridge :=
  { source, target, δ, 
    proof := ProofType.htlb hash timeout,
    nt := NT.mk (fun _ _ => 𝟙 _) }  -- simplified NT for now

/-- zk-SNARK bridge constructor. -/
def zkBridge (source target : Chain) (δ : ℕ) (proof : String) (inputs : List String) : Bridge :=
  { source, target, δ,
    proof := ProofType.zkSnark proof inputs,
    nt := NT.mk (fun _ _ => 𝟙 _) }

/-- Threshold signature bridge constructor. -/
def thresholdBridge (source target : Chain) (δ : ℕ) (sigs : List String) (t : ℕ) : Bridge :=
  { source, target, δ,
    proof := ProofType.thresholdSig sigs t,
    nt := NT.mk (fun _ _ => �� _) }

end Bridge 