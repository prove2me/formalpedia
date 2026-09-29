-- Prove2me | Theorems.Thm_lean_workbook_plus_33848
-- name    : lean_workbook_plus_33848
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/f2187f7a-a5aa-421c-8482-8bd7d220374a
-- statement:
--   Prove the inequality $F(x_1,x_2,x_3,x_4)=S_4-\frac{5}{12}{S_1S_3}-\frac{1}{72}{S_1^2S_2}+\frac{1}{72}{S_1^4}\geq0$ for $n=4$, where $S_k=\sum_{i=1}^n{x_i^k}$ and $x_1,x_2,x_3,x_4\in\mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33848 (x1 x2 x3 x4 : ℝ) : (∑ i in Finset.range 4, x1 ^ 4) - (5 / 12) * (∑ i in Finset.range 4, x1 ^ 3) * (∑ i in Finset.range 4, x1) - (1 / 72) * (∑ i in Finset.range 4, x1 ^ 2) ^ 2 + (1 / 72) * (∑ i in Finset.range 4, x1) ^ 4 ≥ 0   :=  by sorry
