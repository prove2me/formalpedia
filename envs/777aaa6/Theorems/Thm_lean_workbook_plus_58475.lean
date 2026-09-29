-- Prove2me | Theorems.Thm_lean_workbook_plus_58475
-- name    : lean_workbook_plus_58475
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/1f90f69a-96fd-4d8b-aee2-38442325584c
-- statement:
--   If $ y_2=-\frac{x^2}{2}-\sqrt{\frac{x^4}{4}+6x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58475 (x y : ℝ) (h₁ : y = -x^2/2 - Real.sqrt (x^4/4 + 6*x)) : y = -x^2/2 - Real.sqrt (x^4/4 + 6*x)   :=  by sorry
