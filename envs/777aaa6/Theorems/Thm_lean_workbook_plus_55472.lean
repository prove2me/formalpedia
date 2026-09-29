-- Prove2me | Theorems.Thm_lean_workbook_plus_55472
-- name    : lean_workbook_plus_55472
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/20bc2264-e871-4795-82a7-99a9482066bd
-- statement:
--   Show that there does not exist rational numbers $x$ and $y$ such that $x^4 = 2y^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55472 : ¬∃ (x y : ℚ), x^4 = 2*y^2   :=  by sorry
