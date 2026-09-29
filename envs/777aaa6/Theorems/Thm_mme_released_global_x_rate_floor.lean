-- Prove2me | Theorems.Thm_mme_released_global_x_rate_floor
-- name    : mme_released_global_x_rate_floor
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T11:56:33.821986+00:00
-- url     : https://prove2.me/theorems/5db10e3e-def1-46fa-8f23-4122a8794d3e
-- title:
--   Numerical global X-rate floors for all six exact released orientations
-- statement:
--   For the exact published profile in each of six orientations, its X coarse entropy minus the maximum-entropy penalty in natural-log units is at least the corresponding rational rateFloor. The six floors are 1.490665312, 1.490664887, 1.490666224, 1.490666463, 1.490663625 and 1.490666061 per original block.
-- source:
--   Numerical global X-rate certification for the exact ReleasedGlobal candidate from More Asymmetry, https://arxiv.org/html/2404.16349v2#S5 . Y/Z numerical rates and whole-interface recursive continuation remain separate.

import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric MME.MoreAsymmetryExactSeed MME.RegionRate MME.RecursiveThinSplit MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 3000

theorem mme_released_global_x_rate_floor (o : Fin 6) :
    (rateFloor o : ℝ) ≤ (profile o).coarse 0 0 -
      Real.log 2 * entropyPenalty ((profile o).1 0) := by
  sorry
