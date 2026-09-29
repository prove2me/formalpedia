-- Prove2me | Theorems.Thm_lean_workbook_plus_81192
-- name    : lean_workbook_plus_81192
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/728811ab-7c78-4110-b4f2-bb74430b8653
-- statement:
--   Let $a_i=e^{x_i}$ . Hence, $\sum\limits_{i=1}^nx_i=0$ and we need to prove that $\sum\limits_{i=1}^nf(x_i)\geq0$ , \n where $f(x)=\frac{1}{\sqrt{1+(n^2-1)e^x}}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81192 (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i = 0) :
    0 ≤ ∑ i, 1 / Real.sqrt (1 + (n ^ 2 - 1) * Real.exp (x i))   :=  by sorry
