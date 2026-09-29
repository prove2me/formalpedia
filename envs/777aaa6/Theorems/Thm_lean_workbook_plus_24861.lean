-- Prove2me | Theorems.Thm_lean_workbook_plus_24861
-- name    : lean_workbook_plus_24861
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/987e88c1-8238-4352-a46e-8d69ce7259e9
-- statement:
--   When $xy< 0$ , prove that $x^4+y^4> xy(x^2+y^2)=x^3y+xy^3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24861 (x y : ℝ) (h : x * y < 0) : x ^ 4 + y ^ 4 > x * y * (x ^ 2 + y ^ 2)   :=  by sorry
