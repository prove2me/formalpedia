-- Prove2me | Theorems.Thm_lean_workbook_plus_20190
-- name    : lean_workbook_plus_20190
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/23fb6072-014f-427f-824b-75d5da066671
-- statement:
--   For $ f(x)=\\left\\{\\begin{array}{cl} e^{-\\frac{1}{x^2}} & x\\neq 0\\\\ 0 & x=0\\end{array}\\right.,$ prove that $ f^{(n)}(0)=0$ ( $ n$ -th-derivative at $ x=0$ is 0).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20190 : ∀ n, (fun x => if x = 0 then (0 : ℝ) else exp (-1/(x^2))) n = 0   :=  by sorry
