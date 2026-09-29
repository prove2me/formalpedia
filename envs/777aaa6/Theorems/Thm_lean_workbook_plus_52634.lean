-- Prove2me | Theorems.Thm_lean_workbook_plus_52634
-- name    : lean_workbook_plus_52634
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/6bd24d35-c17b-4423-9f90-cf26a50d5b37
-- statement:
--   Prove that the equation $2019x + 1 = y^2$ has no integer solutions $(x, y)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52634 : ¬ (∃ x y : ℤ, 2019*x + 1 = y^2)   :=  by sorry
