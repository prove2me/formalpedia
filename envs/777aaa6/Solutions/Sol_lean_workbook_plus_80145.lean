-- Prove2me | solution 1 for lean_workbook_plus_80145
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:52.108664+00:00
-- url     : https://prove2.me/submissions/d8e41079-960b-4f76-93ff-48ce6957d1c2

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (a b z n : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < z ∧ 0 < n)
    (h₁ : 3 * z = 2 * b) (h₂ : (n - 27) / a = 27 / (2 * b))
    (h₃ : (n - 18) / a = 18 / b) : n = 54 := by
  have hb : b ≠ 0 := ne_of_gt h₀.2.1
  have ha : a ≠ 0 := ne_of_gt h₀.1
  have hb2 : 2 * b ≠ 0 := mul_ne_zero (by norm_num) hb
  have heq2 := (div_eq_div_iff ha hb2).mp h₂
  have heq3 := (div_eq_div_iff ha hb).mp h₃
  have hprod : b * (n - 54) = 0 := by nlinarith [heq2, heq3]
  have hn := (mul_eq_zero.mp hprod).resolve_left hb
  linarith
