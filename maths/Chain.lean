/--
Enumerates the blockchain indices used in examples and tests.  At this
stage we only model two EVM-compatible chains but more can be added as
additional constructors.
-/
inductive Chain
  | polygon
  | arbitrum
  deriving DecidableEq, Repr

namespace Chain

instance : Inhabited Chain := ⟨polygon⟩

end Chain 