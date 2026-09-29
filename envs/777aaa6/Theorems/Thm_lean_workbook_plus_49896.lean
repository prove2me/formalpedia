-- Prove2me | Theorems.Thm_lean_workbook_plus_49896
-- name    : lean_workbook_plus_49896
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3882d1b4-5cb1-40bb-b057-8757c8c50a94
-- statement:
--   Solve: $|4x + 3| - |x + 5| \leq 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49896 (x : ℝ) : |4*x + 3| - |x + 5| ≤ 8 ↔ -16/5 ≤ x ∧ x ≤ 10/3   :=  by sorry
