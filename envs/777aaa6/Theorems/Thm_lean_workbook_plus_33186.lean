-- Prove2me | Theorems.Thm_lean_workbook_plus_33186
-- name    : lean_workbook_plus_33186
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/81f2dab6-67e4-49c2-833c-4a50168df7fb
-- statement:
--   Given $f(x) = e^{cx}$, prove that $f(x) > 0$ for all real x.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33186 (x : ℝ) (c : ℝ) : 0 < exp (c * x)   :=  by sorry
