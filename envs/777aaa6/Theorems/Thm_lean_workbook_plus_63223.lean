-- Prove2me | Theorems.Thm_lean_workbook_plus_63223
-- name    : lean_workbook_plus_63223
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b3cfecf8-7837-4755-84c5-be3f5bb7c691
-- statement:
--   Prove that the sequence $(a_{n})_{n\geq 1}$ defined by $a_{1}=1$ and $a_{n+1}=\frac{2}{n^{2}}\sum_{k=1}^{n}ka_{k}$ is strictly increasing. Is this sequence convergent?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63223 (a : ℕ → ℝ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (2 : ℝ) / (n ^ 2) * ∑ k in Finset.range (n + 1), k * a k) : ∀ n, a n < a (n + 1)   :=  by sorry
