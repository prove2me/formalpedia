-- Prove2me | Theorems.Thm_lean_workbook_plus_23905
-- name    : lean_workbook_plus_23905
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/32d16c41-8681-4511-8269-b92815b5d640
-- statement:
--   Find the minimum value of the sum $g(1) + g(2) + \dots + g(20)$, where $g(n) = n^2 + 1$ for $n \geq 11$ and $g(n) + g(20-n) = n^2 + 1$ for $n < 11$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23905 (g : ℕ → ℕ) (h₁ : ∀ n ≥ 11, g n = n^2 + 1) (h₂ : ∀ n < 11, g n + g (20 - n) = n^2 + 1) : 1350 ≤ ∑ i in Finset.range 20, g i   :=  by sorry
