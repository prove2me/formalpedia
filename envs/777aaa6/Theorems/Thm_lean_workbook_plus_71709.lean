-- Prove2me | Theorems.Thm_lean_workbook_plus_71709
-- name    : lean_workbook_plus_71709
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5f2d1864-5664-4058-b54f-721d62ad3d75
-- statement:
--   Evaluate the limit $ A=\lim_{x\rightarrow 0}\frac{e^x-1-x-x^2/2-x^3/6-x^4/24}{x^5}$ without using hopital rule or taylor series.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71709 (A : ℝ) (x : ℝ) (hx: x = 0) : (exp x - 1 - x - x^2 / 2 - x^3 / 6 - x^4 / 24) / x^5 = 1 / 120   :=  by sorry
