-- Prove2me | Theorems.Thm_lean_workbook_plus_36058
-- name    : lean_workbook_plus_36058
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/26cc17f1-1196-4f87-883f-9158b3041499
-- statement:
--   Prove that for all real numbers $x$, $|\frac{x^3-x^2}{x^4+x^2+1}| \leq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36058 (x : ℝ) : |(x^3 - x^2) / (x^4 + x^2 + 1)| ≤ 1   :=  by sorry
