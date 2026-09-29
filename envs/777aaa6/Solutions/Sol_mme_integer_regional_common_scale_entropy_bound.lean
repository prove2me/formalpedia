-- Prove2me | solution 1 for mme_integer_regional_common_scale_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T21:18:52.379307+00:00
-- url     : https://prove2.me/submissions/d7dd4546-efa7-491a-b67c-4aedbd7f8302

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_physical_hash_load_entropy_bounds
import Theorems.Thm_mme_common_hash_scale_real_upper_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem solution {ell M : ℕ} {P : ProfiledCW.Predicate M} (D : IntegerStep ell M P) :
    0 ≤ scaleExponent D.total D.n D.m D.mu D.epsilon ∧
    (D.scale : ℝ) ≤ scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell *
      Real.exp (scaleExponent D.total D.n D.m D.mu D.epsilon) := by
  have h := mme_regional_physical_hash_load_entropy_bounds D.total D.n D.m D.mu D.repairScale
    D.epsilon D.epsilon_pos.le D.reference D.reference_target
  let theta := scaleExponent D.total D.n D.m D.mu D.epsilon
  let L := loadFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell
  have hL : 0 ≤ L := by dsimp [L,loadFactor,polynomialFactor,ambientFactor]; positivity
  have he : 1 ≤ Real.exp theta := Real.one_le_exp_iff.mpr h.1
  have hs := mme_common_hash_scale_real_upper_bound D.half
    (loadNum D.total D.m D.repairScale (fun i ↦ D.mu (yzMode i)) D.keep) (loadDen D.m)
    (L * Real.exp theta) (mul_nonneg hL (Real.exp_pos _).le) h.2
  refine ⟨h.1,hs.trans ?_⟩
  change (D.half : ℝ) + 2 + L * Real.exp theta ≤ ((D.half : ℝ) + 2 + L) * Real.exp theta
  have hh := mul_le_mul_of_nonneg_left he (show (0 : ℝ) ≤ (D.half : ℝ) + 2 by positivity)
  nlinarith
