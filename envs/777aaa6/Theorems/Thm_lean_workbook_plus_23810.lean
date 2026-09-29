-- Prove2me | Theorems.Thm_lean_workbook_plus_23810
-- name    : lean_workbook_plus_23810
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f7d07763-086e-44eb-983d-b1bf72cc1090
-- statement:
--   Prove that if $a$ is a root of equation $ x^3 - 3x +1 = 0 $ then also $a^2 -2 $ is a root of the equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23810 (a : ℝ) (h : a^3 - 3*a + 1 = 0) : (a^2 - 2)^3 - 3*(a^2 - 2) + 1 = 0   :=  by sorry
