/--
Bundles – finite composites of protocol + bridge morphisms in the total
Grothendieck category `∫ F` together with a repayment arrow that proves
atomicity (all-or-nothing behaviour).

For the thin bicategory on `∫ F`, 2-cells are equalities of morphisms, so
providing an equality `repay ≫ f = 𝟙 start` is exactly a witness that the
composite 1-morphism is *invertible* (with `repay` as inverse).
-/

import Grothendieck.Construction

open CategoryTheory

universe u

namespace Stack

open Grothendieck

/--
A *Bundle* describes an atomic cross-chain execution sequence:
• `forward` is the composite of protocol steps and bridge hops.
• `repay` is the refund path supplying the inverse morphism.
• `atomicity` is the 2-cell (equality) showing the round-trip equals
  the identity on the start object.
-/
structure Bundle where
  start   : TotalObj
  finish  : TotalObj
  forward : Hom start finish
  repay   : Hom finish start
  atomicity : repay ≫ forward = id start

end Stack 