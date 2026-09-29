-- Prove2me | solution 2 for mme_omega_lt_CW
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:31:37.764077+00:00
-- url     : https://prove2.me/submissions/8161f4d9-0278-433f-a3d3-e08e5ed154ed
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_le_of_subrank_capacity_poly
import Theorems.Thm_mme_CW_subrank_capacity_poly_lower
import Theorems.Thm_mme_CW_border_rank_le
import Theorems.Thm_mme_CW_numeric_optimum

open MME

universe u

theorem solution {K : Type u} [Field K] : matMulExp K < 2376 / 1000 := by
  have hbridge : matMulExp_strassen K ≤ Real.log 8 / Real.log (5/2) :=
    mme_omega_le_of_subrank_capacity_poly
      (mme_CW_border_rank_le (K := K) 6)
      (by norm_num : ((8 : ℕ) : ℝ) ≤ 8)
      (by norm_num : (1 : ℝ) ≤ 8)
      (by norm_num : (1 : ℝ) < 5 / 2)
      mme_CW_subrank_capacity_poly_lower
  have hnum := mme_CW_numeric_optimum
  calc matMulExp K
      = matMulExp_strassen K               := mme_omega_eq_strassen
    _ ≤ Real.log 8 / Real.log (5/2)        := hbridge
    _ < 2376 / 1000                        := hnum
