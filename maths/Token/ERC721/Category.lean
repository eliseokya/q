import Mathlib
import EVM.Category
import Internal.Core

/-!
# ERC-721 Ownership Category (𝓣₇₂₁) – Refined Version

* Objects – token IDs (`Nat`).
* Morphisms – lists of primitive `transfer` operations.
* Identity – empty list; composition – list append.
* `State` now tracks ownership (`owner : TokenID → Option Address`).
* `step` updates ownership iff   sender matches current owner.
* Functor `F_nft` (parameterised by contract address) maps actions to
  `EVM.Trace` and preserves identities, composition, and associativity.
-/

open Classical

namespace ERC721

abbrev Address := String
abbrev TokenID := Nat

/-- Primitive transfer of a token from `from` to `to`. -/
structure Prim where
  from : Address
  to   : Address
  id   : TokenID
  deriving Repr, DecidableEq

abbrev Action := List Prim

/-- Identity action – empty list. -/
instance : Contract.HasId Action where
  idAct := []

/-- Composition – list append. -/
instance : Contract.HasComp Action where
  compAct := List.append

/-- Ownership state: mapping from token ID to optional owner address. -/
structure State where
  owner : TokenID → Option Address

namespace State
/-- Helper: perform a transfer if the `from` matches current owner. -/
@[simp]
def transfer (σ : State) (p : Prim) : State :=
  match σ.owner p.id with
  | some o =>
      if h : o = p.from then
        { owner := fun tid => if tid = p.id then some p.to else σ.owner tid }
      else σ   -- invalid sender, ignore
  | none   => σ -- unminted token, ignore
end State

end State

/-- Step for a single primitive. -/
@[simp]
def stepPrim : Prim → State → State := fun p σ => σ.transfer p

/-- Fold a list of actions left-to-right. -/
@[simp]
partial def step : Action → State → State
  | [],     σ => σ
  | a::as, σ => step as (stepPrim a σ)

open Contract

/-- Package into `Spec`. -/
def spec : Spec := { State := State, Action := Action, step := step }

/-- Prove small-category laws. -/
instance : IsCategory spec := by
  refine {
    id_left := ?_,
    id_right := ?_,
    assoc := ?_
  }
  · intro a σ; simp [HasComp.compAct, HasId.idAct, step]
  · intro a σ; simp [HasComp.compAct, HasId.idAct, step, List.append_nil]
  · intro a b c σ; simp [HasComp.compAct, step, List.append_assoc]

/-- Compile a primitive transfer to a placeholder CALL opcode. -/
@[simp]
def compilePrim (_ : Prim) : EVM.OpCode := .CALL

@[simp]
def compile (act : Action) : EVM.Trace :=
  let n := act.length
  {
    ops    := List.repeat (.CALL) n,
    gas    := n,
    diff   := { updates := act.map (fun p => toString p) },
    status := .success
  }

open EVM

lemma compile_id : compile (HasId.idAct : Action) = idTrace := by
  simp [compile, HasId.idAct, idTrace]

lemma compile_pres (a b : Action) :
    comp (compile a) (compile b) = some (compile (a ++ b)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append]

/-- Parameters characterising a deployed ERC-721 contract. -/
structure NFTParams where
  address : Address
  deriving Repr, DecidableEq

variable (P : NFTParams)

/-- Functor on morphisms; objects irrelevant for now. -/
@[simp]
def F_nft (a : Action) : EVM.Trace := compile a

lemma F_nft_id : F_nft P (HasId.idAct : Action) = idTrace := by
  simp [F_nft, compile_id]

lemma F_nft_tensor (a b : Action) :
    comp (F_nft P a) (F_nft P b) = some (F_nft P (a ++ b)) := by
  simp [F_nft, compile_pres]

lemma F_nft_assoc (a b c : Action) :
    comp (compile (a ++ b)) (compile c) = comp (compile a) (compile (b ++ c)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append, List.append_assoc, Nat.add_assoc]

end ERC721 