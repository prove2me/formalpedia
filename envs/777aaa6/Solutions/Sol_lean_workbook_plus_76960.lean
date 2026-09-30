-- Prove2me | solution 1 for lean_workbook_plus_76960
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:19:57.647737+00:00
-- url     : https://prove2.me/submissions/067a248d-df86-4599-92da-143ecdab52bf

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (q : ℝ) :
    4 * ((1 - q ^ 2) / 3) ^ 2 + 81 * ((1 + q) ^ 2 * (1 - 2 * q) / 27) ^ 2 ≥
      15 * ((1 - q ^ 2) / 3) ^ 3 := by
  nlinarith [sq_nonneg (q * (q + 1) * (3 * q - 1))]
