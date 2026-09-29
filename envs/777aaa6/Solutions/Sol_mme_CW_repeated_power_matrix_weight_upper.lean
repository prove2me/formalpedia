-- Prove2me | solution 1 for mme_CW_repeated_power_matrix_weight_upper
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:33:05.362991+00:00
-- url     : https://prove2.me/submissions/d650877d-bcfc-445c-a6e8-f192256902e8

import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_border_rank_le
import Theorems.Thm_mme_borderRank_kronPow_le
import Theorems.Thm_mme_degenerates_asymptoticRank_le
import Theorems.Thm_mme_repeated_restriction_asymptoticRank_le

open MME BigOperators
universe u
set_option autoImplicit false

/-- Any matrix family restricted from repeated CW powers satisfies the concrete
asymptotic sum inequality with the exact source multiplicity. -/
theorem solution
    {K : Type u} [Field K] (q N inputs copies : ℕ)
    (a b c : Fin copies → ℕ)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (TensorObj.bigAdd (fun _ : Fin inputs => (CWObj K q).kronPow N))) :
    ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ (matMulExp_strassen K / 3) ≤
      (inputs : ℝ) * (q + 2 : ℕ) ^ N := by
  have hdeg := mme_borderRank_kronPow_le (CWObj K q) N (q + 2)
    (mme_CW_border_rank_le q)
  have hrank := mme_degenerates_asymptoticRank_le hdeg
  have hfamily := mme_repeated_restriction_asymptoticRank_le (by norm_num)
    inputs ((q + 2) ^ N) hrestrict hrank
  have hsum := mme_sum_inequality a b c (inputs * (q + 2) ^ N) (by
    simpa only [Nat.cast_mul, Nat.cast_pow] using hfamily)
  simpa only [Nat.cast_mul, Nat.cast_pow] using hsum


#print axioms solution
