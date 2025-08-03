import Token.ERC20.Category
import EVM.Category

namespace ERC20

open ERC20 EVM Contract

/-- Parameters for a specific ERC-20 token instance. -/
structure TokenParams where
  address   : Address
  decimals  : Nat := 18
  deriving Repr, DecidableEq

variable (P : TokenParams)

/-- Functor on morphisms: reuse `compile`.  Objects are ignored because both
categories collapse objects; we only need morphism mapping for now. -/
@[simp]
def F_token (a : Action) : EVM.Trace := compile a

lemma F_token_id : F_token P (Contract.HasId.idAct : Action) = idTrace := by
  simp [F_token, compile_id]

lemma F_token_tensor (a b : Action) :
    comp (F_token P a) (F_token P b) = some (F_token P (a ++ b)) := by
  simp [F_token, compile_pres]

@[simp]
lemma F_token_assoc (a b c : Action) :
    comp (compile (a ++ b)) (compile c) = comp (compile a) (compile (b ++ c)) := by
  simp [compile, comp, List.length_append, List.map_append, List.repeat_append, List.append_assoc, Nat.add_assoc]

end ERC20 