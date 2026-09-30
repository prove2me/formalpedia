-- Prove2me | solution 1 for lean_workbook_plus_80233
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:44.832103+00:00
-- url     : https://prove2.me/submissions/7f0ea538-8662-4e17-a042-d43c9f14f859

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a b c : ℝ) (h1 : a + b + c > 0)
    (h2 : a * b + b * c + c * a > 0) (h3 : a * b * c > 0) :
    a > 0 ∧ b > 0 ∧ c > 0 := by
  have hpos : ∀ x : ℝ, x ^ 3 - (a + b + c) * x ^ 2 +
      (a * b + b * c + c * a) * x - a * b * c = 0 → 0 < x := by
    intro x hx
    by_contra hxn
    have hxn' : x ≤ 0 := le_of_not_gt hxn
    have hp := mul_nonneg h1.le (sq_nonneg x)
    have hq := mul_nonpos_of_nonneg_of_nonpos h2.le hxn'
    have hr := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg x) hxn'
    nlinarith
  exact ⟨hpos a (by ring), hpos b (by ring), hpos c (by ring)⟩

#print axioms solution
