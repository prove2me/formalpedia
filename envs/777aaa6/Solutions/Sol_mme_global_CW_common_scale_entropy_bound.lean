-- Prove2me | solution 1 for mme_global_CW_common_scale_entropy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T08:56:45.162711+00:00
-- url     : https://prove2.me/submissions/abf758ed-df77-423d-ac3d-9dbf176fcecb

import Definitions.Def_mme_global_CW_entropy_data
import Theorems.Thm_mme_global_CW_hash_load_entropy_bounds
import Theorems.Thm_mme_common_hash_scale_real_upper_bound
open BigOperators MME MME.GlobalCW MME.RegionRate MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution {ell M : ℕ} (D : CountedStage ell M) :
    0 ≤ D.entropyExponent ∧
    (D.scale : ℝ) ≤ D.entropyScaleFactor * Real.exp D.entropyExponent := by
  have h := mme_global_CW_hash_load_entropy_bounds D
  have hL : 0 ≤ D.entropyLoadFactor := by
    unfold CountedStage.entropyLoadFactor polynomialFactor ambientFactor
    positivity
  have he : 1 ≤ Real.exp D.entropyExponent := Real.one_le_exp_iff.mpr h.1
  have hs := mme_common_hash_scale_real_upper_bound D.degree D.num D.den
    (D.entropyLoadFactor * Real.exp D.entropyExponent)
    (mul_nonneg hL (Real.exp_pos _).le) h.2
  refine ⟨h.1,hs.trans ?_⟩
  change (D.degree : ℝ) + 2 + D.entropyLoadFactor * Real.exp D.entropyExponent ≤
    ((D.degree : ℝ) + 2 + D.entropyLoadFactor) * Real.exp D.entropyExponent
  have hh := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (D.degree : ℝ) + 2)
  nlinarith
