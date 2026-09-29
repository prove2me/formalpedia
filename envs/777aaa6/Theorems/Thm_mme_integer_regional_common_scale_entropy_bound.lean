-- Prove2me | Theorems.Thm_mme_integer_regional_common_scale_entropy_bound
-- name    : mme_integer_regional_common_scale_entropy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T21:17:15.515277+00:00
-- url     : https://prove2.me/theorems/861e2642-fd76-47c6-a4d6-0fc3d4cdd0d8
-- title:
--   The actual integer step has the summed regional entropy scale
-- statement:
--   Prove the upper bound on the actual computed common scale of every IntegerStep, with the minimum of the three complete regional entropy sums and explicit finite polynomial factors. No scale, load, or entropy estimate is assumed.
-- source:
--   The More Asymmetry matrix multiplication campaign, https://arxiv.org/html/2404.16349v2#S6 . Uniform bounds for the actual common hash construction; the numerical surplus certificate remains separate.

import Definitions.Def_mme_regional_entropy_copy_bound
import Definitions.Def_mme_regional_entropy_copy_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem mme_integer_regional_common_scale_entropy_bound {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStep ell M P) :
    0 ≤ scaleExponent D.total D.n D.m D.mu D.epsilon ∧
    (D.scale : ℝ) ≤ scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell *
      Real.exp (scaleExponent D.total D.n D.m D.mu D.epsilon) := by sorry
