-- Prove2me | solution 1 for lean_workbook_plus_80900
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:14:28.589189+00:00
-- url     : https://prove2.me/submissions/af7877b0-2387-4303-8e54-99b59462b377

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (a b c d : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ d)
    (h2 : a + b + c + d = 2) : a ^ 2 + 2 * b * c + d ^ 2 ≥ 1 := by
  nlinarith [h1.1, h1.2.1, h1.2.2]
