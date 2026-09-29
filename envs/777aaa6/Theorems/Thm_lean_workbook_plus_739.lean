-- Prove2me | Theorems.Thm_lean_workbook_plus_739
-- name    : lean_workbook_plus_739
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/275788e7-00ed-49a5-91d3-100c51480d22
-- statement:
--   If $f(x)$ is monic quartic polynomial such that $f(-1)=-1$ , $f(2)=-4$ , $f(-3)=-9$ , and $f(4)=-16$ , find $f(1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_739 (f : ℝ → ℝ) (hf : f = λ x => x^4 + ax^3 + bx^2 + cx + d) : f (-1) = -1 ∧ f 2 = -4 ∧ f (-3) = -9 ∧ f 4 = -16 → f 1 = -1   :=  by sorry
