-- Prove2me | solution 1 for mme_omega_lt_2371177
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-28T14:52:49.518991+00:00
-- url     : https://prove2.me/submissions/6c2adf5e-4233-4879-be69-3054895e2b62
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_alphaevolve_level4_global_graded_surplus
import Theorems.Thm_mme_global_CW_graded_start_omega_bound
open MME MME.GlobalCW
set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 2371177 / 1000000 := by
  obtain ⟨n, D, _hn, _hi, hv, hs⟩ := mme_alphaevolve_level4_global_graded_surplus
  have h := mme_global_CW_graded_start_omega_bound (K := K) D ((2371177 : ℝ) / 3000000) hv hs
  have e : (3 : ℝ) * ((2371177 : ℝ) / 3000000) = 2371177 / 1000000 := by norm_num
  rwa [e] at h
