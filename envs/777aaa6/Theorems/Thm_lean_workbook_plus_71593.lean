-- Prove2me | Theorems.Thm_lean_workbook_plus_71593
-- name    : lean_workbook_plus_71593
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/12457cc0-df73-4948-bcac-1cfd7094c2b8
-- statement:
--   Determine the correct piecewise function representation of the absolute value function $y=|x|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71593 (x : ℝ) : |x| = if x < 0 then -x else x   :=  by sorry
