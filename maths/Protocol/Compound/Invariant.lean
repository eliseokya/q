import Protocol.Compound.Base
import Protocol.Compound.Step
import Protocol.Compound.Alg.Accrue
import Mathlib.Tactic.Linarith

namespace Compound

open Compound.Prim

-- count accrue occurrences in an action list
@[simp] def accCount : Action → Nat
  | [] => 0
  | Prim.accrue :: tl => accCount tl + 1
  | _ :: tl => accCount tl

open Compound.Alg

/-- Collateral ratio preserved provided initial collateral covers all future interest accruals. -/
lemma healthy_preserved_with_margin
    (acts : Action) (l : Ledger)
    (h_margin : l.s ≥ (1 + r) ^ accCount acts * l.b)
    (hb : 0 ≤ l.b) :
    healthy (step acts l) := by
  induction acts with
  | nil =>
      simpa [step, accCount, healthy] using
        margin_implies_healthy (k:=0) (s:=l.s) (b:=l.b) (h:=by
          simpa using h_margin) hb
  | cons p tl ih =>
      match p with
      | accrue =>
          -- use margin_after_one to get margin for ledger after accrue
          have hHead := margin_after_one (p:=Prim.accrue) (s:=l.s) (b:=l.b)
                            (k:=accCount (Prim.accrue :: tl)) h_margin hb
          rcases hHead with ⟨k', hInv', hk'⟩
          -- apply IH to tail with new ledger and new exponent
          have hRec := ih (applyPrim Prim.accrue l) hInv' hb
          simpa [step] using hRec
      | supply amt =>
          -- new margin for supply: collateral increases
          have h_margin_next : (l.s + amt) ≥ (1 + r) ^ accCount tl * l.b :=
            margin_stable_supply (k:=accCount tl)
              (hinv:=by
                -- rewrite original margin using accCount_cons
                simpa [accCount_cons, if_neg (by decide)] using h_margin)
              (ha:=by linarith)
          -- healthy after supply action
          have hHealthy := healthy_after_supply (l:=l) (a:=amt)
            (h:=margin_implies_healthy (k:=accCount tl) (s:=l.s) (b:=l.b)
                (h:=by
                  simpa [accCount_cons, if_neg (by decide)] using h_margin)
                hb)
          -- apply IH on tail
          have hRec := ih (applyPrim (Prim.supply amt) l) h_margin_next hb
          simpa [step] using hRec
      | repay amt =>
          -- margin after repay: debt decreases
          have h_margin_next : l.s ≥ (1 + r) ^ accCount tl * max 0 (l.b - amt) :=
            margin_stable_repay (k:=accCount tl)
              (hinv:=by simpa [accCount_cons, if_neg (by decide)] using h_margin)
              (ha:=by linarith)
          -- healthy after repay action
          have hHealthy := healthy_after_repay (l:=l) (a:=amt)
            (h:=margin_implies_healthy (k:=accCount tl) (s:=l.s) (b:=l.b)
                (h:=by simpa [accCount_cons, if_neg (by decide)] using h_margin)
                hb)
          -- apply IH
          have hb' : 0 ≤ max 0 (l.b - amt) := by apply le_max_left
          have hRec := ih (applyPrim (Prim.repay amt) l) h_margin_next hb'
          simpa [step] using hRec

end Compound 