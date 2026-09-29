-- Prove2me | Theorems.Thm_mme_released_global_x_entropy_bridge
-- name    : mme_released_global_x_entropy_bridge
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:57:14.193708+00:00
-- url     : https://prove2.me/theorems/0f7515c0-4b33-408e-a840-952b4e3229e2
-- title:
--   Connect the exact global profile to its dual entropy certificate
-- statement:
--   For each orientation of the published ReleasedGlobal.profile, bound its actual maximum-entropy penalty by the exact product-reference cross-entropy, and identify its X coarse entropy and joint entropy with the 9- and 45-entry rational certificate vectors.
-- source:
--   Numerical global X-rate certification for the exact ReleasedGlobal candidate from More Asymmetry, https://arxiv.org/html/2404.16349v2#S5 . Y/Z numerical rates and whole-interface recursive continuation remain separate.

import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000

theorem mme_released_global_x_entropy_bridge (o : Fin 6) :
    Real.log 2 * entropyPenalty ((profile o).1 0) ≤
      -(∑ s : Fin 45, (alphaQ o s : ℝ)*Real.log (dualQ o s : ℝ)) -
        entropy ((profile o).1 0) ∧
    (profile o).coarse 0 0 = ∑ j : Fin 9, Real.negMulLog (marginalQ o 0 j : ℝ) ∧
    entropy ((profile o).1 0) = ∑ s : Fin 45, Real.negMulLog (alphaQ o s : ℝ) := by
  sorry
