/--
Snapshot predicates for restricting `EVM.Trace`s to those valid up to a
particular block height on a given chain.  For now we have no concrete
ledger, so **every successful trace** is deemed valid.  The definition
is a placeholder and will be tightened once we add real state.
-/

import Chain
import EVM.Trace

open EVM

universe u

namespace Snapshot

/-- Predicate: trace `tr` is admissible on chain `L` by block `t`.  For
now we only require that the trace terminates successfully. -/
@[simp]
def validTrace (L : Chain) (t : ℕ) (tr : Trace) : Prop :=
  tr.status = ExecStatus.success

end Snapshot 