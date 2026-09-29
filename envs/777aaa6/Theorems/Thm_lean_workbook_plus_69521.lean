-- Prove2me | Theorems.Thm_lean_workbook_plus_69521
-- name    : lean_workbook_plus_69521
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5fadf4c4-c175-4ce7-8ad0-835927428a20
-- statement:
--   Prove that the sequence $ \left( a_n \right)_{n\ge 1} $ with $ a_1=1 $ and defined by the recursive relation $ a_{n+1}=\frac{2}{n^2}\sum_{k=1}^n ka_k $ is nondecreasing. Is it convergent?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69521 (n : ℕ) (a : ℕ → ℝ) (a1 : a 0 = 1) (a_rec : ∀ n, a (n + 1) = (2 / n ^ 2) * ∑ k in Finset.range (n + 1), k * a k) : ∀ n, a n ≤ a (n + 1)   :=  by sorry
