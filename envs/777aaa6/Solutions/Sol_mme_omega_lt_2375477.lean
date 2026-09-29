-- Prove2me | solution 1 for mme_omega_lt_2375477
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T08:21:05.083878+00:00
-- url     : https://prove2.me/submissions/bc452d4d-6326-4cfe-8ffc-f8d3541f0822

import Theorems.Thm_mme_omega_eq_strassen
import Theorems.Thm_mme_omega_strassen_lt_2375477

open MME

universe u

/-- Platform-ready proof matching the final printed-endpoint mission. -/
theorem solution {K : Type u} [Field K] :
    matMulExp K < 2375477 / 1000000 := by
  rw [mme_omega_eq_strassen]
  exact mme_omega_strassen_lt_2375477

