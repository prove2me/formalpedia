-- Prove2me | Theorems.Thm_lean_workbook_plus_2048
-- name    : lean_workbook_plus_2048
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/708b5936-4988-4b07-bd45-2ec77a455817
-- statement:
--   Explain the step: $2^{log_{2}5-2} = \frac{2^{log_{2}5}}{2^{2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2048 : (2:ℝ)^(Real.logb 2 5 - 2) = (2:ℝ)^(Real.logb 2 5) / (2:ℝ)^2   :=  by sorry
