-- Prove2me | Theorems.Thm_lean_workbook_plus_66293
-- name    : lean_workbook_plus_66293
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/1cbc4e25-7cea-4501-a55b-9962c492b602
-- statement:
--   Since $1 < k < 2$ we may set $k = 2\cos \theta$ for some $\theta \in \left(0, \frac{\pi}{3}\right)$ . Now a simple induction shows the surprising result that for all $n \geqslant 1$ , $$b_n = \frac{\sin n\theta}{\sin \theta}.$$ Now, the first part of the problem trivialises since $B = \frac{1}{\sin \theta} = \frac{2}{\sqrt{4-k^2}}$ works fine.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_66293  (k : ℝ)
  (b : ℕ → ℝ)
  (h₀ : 1 < k ∧ k < 2)
  (h₁ : b 0 = 1)
  (h₂ : ∀ n, b (n + 1) = k * b n - b (n - 1)) :
  ∃ B, ∀ n, b n = B * Real.sin (n * θ) / Real.sin θ   :=  by sorry
