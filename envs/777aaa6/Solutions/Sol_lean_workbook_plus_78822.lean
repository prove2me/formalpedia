-- Prove2me | solution 1 for lean_workbook_plus_78822
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:36:51.556578+00:00
-- url     : https://prove2.me/submissions/af527783-14cd-41e8-b3c9-debf4f2afff1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution : ¬ (∀ (f : ℤ → ℝ),
    (∀ n, 1000 ≤ n → f n = n - 3) →
    (∀ n, n < 1000 → f n = f (n + 5)) → f 94 = 91) := by
  intro h
  let f : ℤ → ℝ := fun n => if 1000 ≤ n then (n : ℝ) - 3
    else ((997 + (n - 1000) % 5 : ℤ) : ℝ)
  have hf : ∀ n, 1000 ≤ n → f n = n - 3 := by
    intro n hn
    simp [f, hn]
  have hg : ∀ n, n < 1000 → f n = f (n + 5) := by
    intro n hn
    have hn' : ¬ 1000 ≤ n := by omega
    by_cases hnext : 1000 ≤ n + 5
    · have hm : (n - 1000) % 5 = n - 995 := by omega
      simp [f, hn', hnext, hm]
      push_cast
      ring
    · have hm : (n + 5 - 1000) % 5 = (n - 1000) % 5 := by omega
      simp [f, hn', hnext, hm]
  have hbad := h f hf hg
  norm_num [f] at hbad
