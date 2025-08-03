import Protocol.UniV2.Base

namespace UniV2

open Classical
open Pool

/-- Constant-product swap (no fee, perfect precision). -/
@[simp]
def step (a : Action) (p : Pool) : Pool :=
  if h : a.dx = 0 then p else
    let dx := a.dx
    let x' := p.x + dx
    let dy := (dx * p.y) / x'
    { x := x', y := p.y - dy }

end UniV2