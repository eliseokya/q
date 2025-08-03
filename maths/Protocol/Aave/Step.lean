import Protocol.Aave.Base

namespace Aave

/-- Primitive actions: deposit collateral, borrow, repay. -/
inductive Prim where
  | deposit (amt : ℚ)
  | borrow  (amt : ℚ)
  | repay   (amt : ℚ)
  deriving Repr

abbrev Action := List Prim

/-- Identity action = empty list. -/
instance : Contract.HasId Action where
  idAct := []

instance : Contract.HasComp Action where
  compAct := List.append

@[simp]
def applyPrim : Prim → Ledger → Ledger
  | Prim.deposit a, l => { l with c := l.c + a }
  | Prim.borrow a,  l =>
      if h : l.c ≥ l.d + a then { l with d := l.d + a } else l
  | Prim.repay a,   l =>
      let newD := max 0 (l.d - a)
      { l with d := newD }

@[simp]
partial def step : Action → Ledger → Ledger
  | [],     l => l
  | p::ps, l => step ps (applyPrim p l)

end Aave 