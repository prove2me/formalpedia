-- Prove2me | solution 1 for mme_omega_lt_2522
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:06:36.380845+00:00
-- url     : https://prove2.me/submissions/d417c826-b739-49c4-8c89-8b4928ac38a3

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_2522

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 1261 / 500 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt_2522
