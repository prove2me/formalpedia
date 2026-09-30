-- Prove2me | solution 1 for lean_workbook_plus_79890
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:46.03779+00:00
-- url     : https://prove2.me/submissions/a6cead42-a387-46cf-9d85-6eb64309ba29

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ,
    (a * b / c ^ 2 + a * c / b ^ 2 + b * c / a ^ 2 + a ^ 2 / (b * c) +
      b ^ 2 / (a * c) + c ^ 2 / (a * b) - 6) ≥ 0) := by
  intro h
  have hbad := h 0 0 0
  simp only [zero_mul, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div, zero_add] at hbad
  exact (by norm_num : ¬ ((0 : ℝ) - 6 ≥ 0)) hbad
