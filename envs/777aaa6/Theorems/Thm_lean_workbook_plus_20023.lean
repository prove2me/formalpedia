-- Prove2me | Theorems.Thm_lean_workbook_plus_20023
-- name    : lean_workbook_plus_20023
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/99f8f490-bd73-487e-a83b-a6f0e97febbf
-- statement:
--   Prove that $cos2A = 2cos^2A - 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20023 (A : ℝ) : Real.cos (2 * A) = 2 * (Real.cos A)^2 - 1   :=  by sorry
