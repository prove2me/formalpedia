-- Prove2me | Theorems.Thm_lean_workbook_plus_70678
-- name    : lean_workbook_plus_70678
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/59883563-2bb5-48b2-804f-3d928e76b4bf
-- statement:
--   and we get the equation $$y(6y+5)=0$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70678 (y : ℝ) : y * (6 * y + 5) = 0 ↔ y = 0 ∨ y = -5/6   :=  by sorry
