-- Prove2me | solution 3 for mme_omega_lt_CW
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T15:03:18.84398+00:00
-- url     : https://prove2.me/submissions/6dee49e1-f06f-47d6-85f0-a6df9d47abfa

import Definitions.Def_mme_omega
import Theorems.Thm_mme_omega_lt_2376
open MME
set_option autoImplicit true

/-- The Coppersmith–Winograd bound `ω < 2.376`, obtained from the platform theorem
`mme_omega_lt_2376 : matMulExp K < 297 / 125` and the identity `2376 / 1000 = 297 / 125`. -/
theorem solution {K : Type u} [Field K] : matMulExp K < 2376 / 1000 := by
  have h : matMulExp K < 297 / 125 := mme_omega_lt_2376 (K := K)
  have heq : (2376 : ℝ) / 1000 = 297 / 125 := by norm_num
  rw [heq]
  exact h
