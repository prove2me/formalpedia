-- Prove2me | Theorems.Thm_lean_workbook_plus_52488
-- name    : lean_workbook_plus_52488
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/282b4fdc-74a8-44f8-b708-970fd7bf463a
-- statement:
--   2*LHS is: \n $-\sqrt{6}+2\sqrt{3}-3\sqrt{2}+2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52488 (x : ℝ) : 2 * (-(Real.sqrt 6) + 2 * (Real.sqrt 3) - 3 * (Real.sqrt 2) + 2) = -2 * Real.sqrt 6 + 4 * Real.sqrt 3 - 6 * Real.sqrt 2 + 4   :=  by sorry
