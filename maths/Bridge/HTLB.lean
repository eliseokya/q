/--
Example bridge value: Hashed Time Locked Bridge (HTLB) simplified to
zero‐delay and identity natural transformation (i.e. it stays on the
same chain).  Serves as a placeholder until concrete cross‐chain
implementations are added.
-/

import Bridge.Types
import Chain

namespace Bridge

open CategoryTheory

/-- HTLB placeholder that operates within a single chain `L` with zero
latency. -/
@[simp]
def HTLBSame (L : Chain) : Bridge.Bridge L L where
  δ := 0
  nt := { η := 𝟙 (Stack.FL L) }

end Bridge 