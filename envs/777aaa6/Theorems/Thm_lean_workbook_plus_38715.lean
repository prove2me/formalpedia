-- Prove2me | Theorems.Thm_lean_workbook_plus_38715
-- name    : lean_workbook_plus_38715
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/87bcda9f-4b6a-40e6-bcfb-a345ff78ee6e
-- statement:
--   Find the intersection point of the lines $y=-\frac{1}{2}x+2$ and $y=2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38715 (x y : ℝ) : (y = -1/2 * x + 2 ∧ y = 2 * x) ↔ (x = 4/5 ∧ y = 8/5)   :=  by sorry
