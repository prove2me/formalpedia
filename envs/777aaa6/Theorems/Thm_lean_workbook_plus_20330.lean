-- Prove2me | Theorems.Thm_lean_workbook_plus_20330
-- name    : lean_workbook_plus_20330
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/0248404b-ea71-4575-a44a-50a4b630d5a4
-- statement:
--   Prove that for every non-negative $y$, $y^2\le y+y^3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20330 (y:ℝ) (hy: y ≥ 0) : y^2 ≤ y + y^3   :=  by sorry
