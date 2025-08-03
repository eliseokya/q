import Mathlib
import EVM.Trace

set_option autoImplicit true

namespace Contract

/-- Core record capturing a contract’s storage state and callable actions. -/
structure Spec where
  State   : Type
  Action  : Type
  step    : Action → State → State

/-- Identity action for a given contract. -/
class HasId (A : Type) where
  idAct : A

/-- Composition of actions. -/
class HasComp (A : Type) where
  compAct : A → A → A

variable {C : Spec}

/-- A small category structure on `C.Action` where objects are states and morphisms are actions. -/
class IsCategory (C : Spec) [HasId C.Action] [HasComp C.Action] : Prop where
  id_left  : ∀ a s, C.step (HasComp.compAct HasId.idAct a) s = C.step a s
  id_right : ∀ a s, C.step (HasComp.compAct a HasId.idAct) s = C.step a s
  assoc    : ∀ a b c s,
    C.step (HasComp.compAct (HasComp.compAct a b) c) s =
    C.step (HasComp.compAct a (HasComp.compAct b c)) s

/-- Placeholder example: we will instantiate this for concrete contracts later. -/
example : True := by trivial

end Contract 