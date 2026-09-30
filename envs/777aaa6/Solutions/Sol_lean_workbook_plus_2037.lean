-- Prove2me | solution 1 for lean_workbook_plus_2037
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T03:27:32.411751+00:00
-- url     : https://prove2.me/submissions/7bb0094d-9a07-4b4c-b830-f56f2055b7db

import Mathlib

theorem solution : ¬ (∀ (f g : ℝ → ℝ),
    (∀ x y, x < y → f x > f y) →
    (∀ x y, x < y → g x > g y) →
    ∀ x y, x < y → (g ∘ f) x > (g ∘ f) y) := by
  intro h
  have hn : ∀ x y : ℝ, x < y → -x > -y := by
    intro x y hxy
    linarith
  have hc := h (fun x => -x) (fun x => -x) hn hn 0 1 (by norm_num)
  have hbad : (1 : ℝ) < 0 := by simpa only [Function.comp_apply, neg_neg] using hc
  exact (not_lt_of_ge (show (0 : ℝ) ≤ 1 by norm_num)) hbad
