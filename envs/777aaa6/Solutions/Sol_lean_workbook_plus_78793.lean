-- Prove2me | solution 1 for lean_workbook_plus_78793
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:52.288182+00:00
-- url     : https://prove2.me/submissions/38811e0a-8a19-4d47-abbd-209aafaeed5a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : ¬ (∀ a b c : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 →
    a * (b + c - a) / (a ^ 2 + 2 * b * c) +
    b * (c + a - b) / (b ^ 2 + 2 * c * a) +
    c * (a + b - c) / (c ^ 2 + 2 * a * b) ≥ 0) := by
  intro h
  have hbad := h 1 0 0 (by norm_num)
  simp only [zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one,
    zero_pow (by decide : (2 : ℕ) ≠ 0), one_pow, zero_div, div_one,
    sub_zero, zero_sub] at hbad
  norm_num at hbad
