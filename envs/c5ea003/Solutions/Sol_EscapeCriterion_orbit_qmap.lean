-- Prove2me | solution 1 for EscapeCriterion.orbit_qmap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T22:45:44.00185+00:00
-- url     : https://prove2.me/submissions/901d9eb3-f818-4942-9e59-eb6649fa8ded

import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
open EscapeCriterion in
theorem solution (c z : ℂ) (n : ℕ) :
    orbit c (MandelbrotEscape.qmap c z) n = orbit c z (n + 1) := by
  unfold orbit
  rw [Function.iterate_succ_apply]
