-- Prove2me | Theorems.Thm_lean_workbook_plus_26407
-- name    : lean_workbook_plus_26407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/b4839598-d8fb-4246-92c4-57ca111f40b8
-- statement:
--   Prove that if $x+y+z=0$ , then $x^3+y^3+z^3=3xyz$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26407 (x y z : ℝ) (h : x + y + z = 0) : x^3 + y^3 + z^3 = 3 * x * y * z   :=  by sorry
