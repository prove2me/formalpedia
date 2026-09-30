-- Prove2me | solution 1 for lean_workbook_plus_72797
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:20:48.409912+00:00
-- url     : https://prove2.me/submissions/fa173902-5cdd-4b4f-a766-32f40ca7b5b5

import Mathlib

theorem positive_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a*b + b*c + c*a ≥ 3*(a+b+c)/(1/a + 1/b + 1/c) := by
  have hs : 0 < 1/a + 1/b + 1/c := by positivity
  have hid : (a*b + b*c + c*a)*(1/a + 1/b + 1/c) - 3*(a+b+c) =
      ((a*b-b*c)^2 + (b*c-c*a)^2 + (c*a-a*b)^2)/(2*a*b*c) := by
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc]
    <;> ring
  have hn : 0 ≤ (a*b + b*c + c*a)*(1/a + 1/b + 1/c) - 3*(a+b+c) := by
    rw [hid]
    positivity
  exact (div_le_iff₀ hs).2 (sub_nonneg.mp hn)

theorem solution (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : 1/a + 1/b + 1/c = 1) :
    a*b + b*c + c*a ≥ 3*(a+b+c)/(1/a + 1/b + 1/c) :=
  positive_bound a b c h₀.1 h₀.2.1 h₀.2.2
