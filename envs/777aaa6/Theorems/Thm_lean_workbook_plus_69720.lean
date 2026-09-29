-- Prove2me | Theorems.Thm_lean_workbook_plus_69720
-- name    : lean_workbook_plus_69720
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/043a67ca-6f15-4e82-88d6-48ea897465ab
-- statement:
--   The function that describes PigeonBoi420's behavior is described by the sequence $a_n=69+\sum_{i=1}^n{3i}$ . We then have the inequality $69+\frac{3n(n+1)}{2}>420$ . Simplifying, we get $3n^2+3n>702$ , so $n^2+n-234>0$ . Using the quadratic formula, our roots are $\frac{-1\pm\sqrt{937}}{2}$ We only care about the positive root, which evaluates to ~ $14.8052$ Therefore, PigeonBoi420 will haul in a number of pigeons greater than 420 in 15 days. So the answer is D.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69720  (n : ℕ)
  (a : ℕ → ℕ)
  (h₀ : ∀ x, a (x + 1) = a x + 3 * x)
  (h₁ : a 1 = 69)
  (h₂ : 420 < a n) :
  15 ≤ n   :=  by sorry
