-- Prove2me | Theorems.Thm_lean_workbook_plus_40069
-- name    : lean_workbook_plus_40069
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/9e2f6263-6526-418a-83d4-f9824bd5db6d
-- statement:
--   Prove that\n(a) if $y=\frac{x^{2}+x+1}{x^{2}+1}$ , then $\frac{1}{2} \leq y \leq \frac{3}{2}$ ,\n(b) if $y= \frac{x^{2}+1}{x^{2}+x+1}$ , then $\frac{2}{3} \leq y \leq 2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40069 (x y : ℝ) (h₁ : y = (x^2 + x + 1) / (x^2 + 1)) : 1 / 2 ≤ y ∧ y ≤ 3 / 2   :=  by sorry
