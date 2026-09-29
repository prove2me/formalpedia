-- Prove2me | solution 3 for mme_omega_lt_237193
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:24:36.565931+00:00
-- url     : https://prove2.me/submissions/c4553c0f-845e-4627-aeb9-9f5fa6b2b97e

import Theorems.Thm_mme_omega_lt_237134
import Mathlib.Tactic.Linarith
open MME
universe u

theorem solution {K : Type u} [Field K] :
    matMulExp K < 237193 / 100000 := by
  have h := mme_omega_lt_237134 (K := K)
  linarith
