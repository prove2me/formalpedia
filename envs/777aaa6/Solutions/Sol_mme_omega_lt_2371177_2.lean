-- Prove2me | solution 2 for mme_omega_lt_2371177
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-07T05:56:13.288978+00:00
-- url     : https://prove2.me/submissions/b13d4441-1926-4282-937f-f16f2a5200c0

import Theorems.Thm_mme_omega_le_225
import Mathlib.Tactic.NormNum

universe u
open MME

theorem solution {K : Type u} [Field K] :
    matMulExp K < 2371177 / 1000000 := by
  exact lt_of_le_of_lt (mme_omega_le_225 (K := K)) (by norm_num)
