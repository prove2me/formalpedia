-- Prove2me | Theorems.Thm_lean_workbook_plus_58811
-- name    : lean_workbook_plus_58811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/df1ad555-471d-4a5f-bea0-084df0701a4d
-- statement:
--   There is no $y\in\mathbb Z$ such that $126y^2=2009$ since LHS is even while RHS is odd.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58811 : ¬∃ y : ℤ, 126 * y ^ 2 = 2009   :=  by sorry
