-- Prove2me | Theorems.Thm_lean_workbook_plus_72204
-- name    : lean_workbook_plus_72204
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a0914547-1841-4195-b785-7a25f0b1472a
-- statement:
--   Express $\cosh3t$ in terms of $\cosh t$ and simplify\n$\cosh3t=\cosh t\bigl(4\cosh^2t-3\bigl)=\cosh^3t\Bigl(4-\frac{3}{\cosh^2t}\Bigr)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72204 (t : ℝ) : Real.cosh (3 * t) = Real.cosh t * (4 * (Real.cosh t)^2 - 3)   :=  by sorry
