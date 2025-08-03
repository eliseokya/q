import Protocol.Compound.Base

namespace Compound

/-- Annualised interest rate per step (could be parameterised). -/
@[simp] def r : ℚ := 1/10 -- 10 % per accrual step

/-- Primitive actions. -/
inductive Prim where
  | accrue
  | supply (amt : ℚ)
  | repay  (amt : ℚ)
  deriving Repr

abbrev Action := List Prim

instance : Contract.HasId Action where idAct := []
instance : Contract.HasComp Action where compAct := List.append

@[simp]
def applyPrim : Prim → Ledger → Ledger
  | Prim.accrue, l => { l with b := l.b * (1 + r) }
  | Prim.supply a, l => { l with s := l.s + a }
  | Prim.repay  a, l => { l with b := max 0 (l.b - a) }

@[simp]
partial def step : Action → Ledger → Ledger
  | [],     l => l
  | p::ps, l => step ps (applyPrim p l)

end Compound 