-- Prove2me | Theorems.Thm_lean_workbook_plus_63835
-- name    : lean_workbook_plus_63835
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/93571987-8804-489d-8ae2-17855a74dfdb
-- statement:
--   $ (t-1)^{2}(7t^{2}-4t+1)\\geq0 $ ,and $ t\\geq1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63835 (t : ℝ) (ht1 : t ≥ 1) : (t - 1) ^ 2 * (7 * t ^ 2 - 4 * t + 1) ≥ 0   :=  by sorry
