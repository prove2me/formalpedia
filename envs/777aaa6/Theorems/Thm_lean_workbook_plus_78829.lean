-- Prove2me | Theorems.Thm_lean_workbook_plus_78829
-- name    : lean_workbook_plus_78829
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/94cdfcdf-a52e-4c5c-9185-80ebc1711e4c
-- statement:
--   Use $ (a^2 - 1)(b^2 - 1)=(ab + 1)^2 - (a + b)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78829 (a b : ℤ) : (a^2 - 1) * (b^2 - 1) = (a * b + 1)^2 - (a + b)^2   :=  by sorry
