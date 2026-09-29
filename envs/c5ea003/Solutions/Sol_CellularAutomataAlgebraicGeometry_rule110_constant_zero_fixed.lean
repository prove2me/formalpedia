-- Prove2me | solution 1 for CellularAutomataAlgebraicGeometry.rule110_constant_zero_fixed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:54:27.787118+00:00
-- url     : https://prove2.me/submissions/ee79479e-eaf8-45d6-af12-2caf714b7309

-- Sol generated from Novelty/CellularAutomataAlgebraicGeometry.lean
import Mathlib
import Definitions.Def_Novelty_CellularAutomataAlgebraicGeometry

/-!
# Elementary cellular automata as polynomial maps

This file formalizes elementary cellular automata on bi-infinite Boolean
configurations.  It identifies the algebraic normal form of Rule 110 and proves
that Rule 0 has one fixed configuration, whereas Rule 204 fixes every
configuration.  An explicit configuration shows that Rule 110 does not have
all states as fixed points.
-/

open CellularAutomataAlgebraicGeometry












open CellularAutomataAlgebraicGeometry in
theorem solution:
    globalUpdate 110 (fun _ : Int => false) = (fun _ => false) := by
  funext i
  norm_num [globalUpdate, localRule, neighborhoodIndex]
