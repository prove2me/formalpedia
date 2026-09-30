-- Prove2me | solution 1 for lean_workbook_plus_77495
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:14:29.38776+00:00
-- url     : https://prove2.me/submissions/6410beda-5a1c-4db8-a368-61f950dfc7ec

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (k a b c d : ℝ) (h1 : 0 < k)
    (h2 : 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d)
    (h3 : a ≤ k ∧ b ≤ k ∧ c ≤ k ∧ d ≤ k) :
    2 * k ^ 2 - k * (a + b + c + d) + a * b + b * c + c * d + d * a ≥ 0 := by
  have hp := mul_nonneg (add_nonneg h2.1 h2.2.2.1)
    (add_nonneg h2.2.1 h2.2.2.2)
  have hq := mul_nonneg (show 0 ≤ 2 * k - (a + c) by linarith [h3.1, h3.2.2.1])
    (show 0 ≤ 2 * k - (b + d) by linarith [h3.2.1, h3.2.2.2])
  nlinarith [hp, hq]
