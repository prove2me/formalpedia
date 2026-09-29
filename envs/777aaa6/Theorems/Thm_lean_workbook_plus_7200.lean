-- Prove2me | Theorems.Thm_lean_workbook_plus_7200
-- name    : lean_workbook_plus_7200
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/421b2671-9c9c-4801-8c84-5307b6228d9b
-- statement:
--   Prove that $y^3 + 2y^2 + 1$ lies between $y^3$ and $(y+1)^3$ for $y > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7200 (y : ℝ) (hy : y > 0) : y^3 < y^3 + 2*y^2 + 1 ∧ y^3 + 2*y^2 + 1 < (y + 1)^3   :=  by sorry
