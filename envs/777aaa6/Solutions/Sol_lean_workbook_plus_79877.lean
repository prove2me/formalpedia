-- Prove2me | solution 1 for lean_workbook_plus_79877
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:51.377525+00:00
-- url     : https://prove2.me/submissions/3058c8e7-28ee-4276-9df4-868d75060afc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b c p q r : ℝ) (h₀ : a + b + c = 0)
    (h₁ : p + q + r = 0) (h₂ : a * p + b * q + c * r = 0) (h₃ : c ≠ 0) :
    2 * b * q + b * r + c * q + 2 * c * r = 0 := by
  have ha : a = -b - c := by linarith
  have hp : p = -q - r := by linarith
  rw [ha, hp] at h₂
  nlinarith [h₂]
