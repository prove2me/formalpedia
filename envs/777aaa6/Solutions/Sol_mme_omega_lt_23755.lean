-- Prove2me | solution 1 for mme_omega_lt_23755
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:19:10.001061+00:00
-- url     : https://prove2.me/submissions/526622f1-984b-40b7-b0f1-510c2f8123b0

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_23755

/-! Platform-ready assembly for the `omega < 2.3755` mission. -/

open MME

universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 4751 / 2000 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt_23755

