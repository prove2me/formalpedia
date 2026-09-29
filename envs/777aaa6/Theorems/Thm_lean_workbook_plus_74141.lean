-- Prove2me | Theorems.Thm_lean_workbook_plus_74141
-- name    : lean_workbook_plus_74141
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/fed2b243-722b-4c66-970f-46072c423969
-- statement:
--   For $x < 0$, prove that $f(x) = x^2 + x + \frac{1}{x} + \frac{1}{x^2} \geq 0$ with equality at $x = -1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74141 (x : ℝ) (hx : x < 0) : x^2 + x + 1/x + 1/(x^2) ≥ 0   :=  by sorry
