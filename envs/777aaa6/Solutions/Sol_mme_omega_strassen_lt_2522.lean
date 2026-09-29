-- Prove2me | solution 1 for mme_omega_strassen_lt_2522
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:06:36.230188+00:00
-- url     : https://prove2.me/submissions/c938ce85-ae2f-45d0-9be5-c18aa9223bf7

import Mathlib.Data.Fin.VecNotation
import Theorems.Thm_mme_asymptotic_sum_inequality
import Theorems.Thm_mme_schonhage_pan_direct_sum
import Theorems.Thm_mme_omega_lt_2522_of_sum_le

open MME BigOperators

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp_strassen K < 1261 / 500 := by
  apply mme_omega_lt_2522_of_sum_le
  have h := mme_asymptotic_sum_inequality
    (K := K)
    ![1, 11, 10]
    ![5, 2, 11]
    ![22, 5, 1]
    156
    mme_schonhage_pan_direct_sum
  norm_num [Fin.sum_univ_succ] at h ⊢
  linarith
