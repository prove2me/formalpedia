-- Prove2me | Theorems.Thm_lean_workbook_plus_15175
-- name    : lean_workbook_plus_15175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/521341d6-072b-4432-a90e-98b6868a7be1
-- statement:
--   Find the values of $b$ from the equation $(b-1)^2(2b+7)=0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15175 (b : ℝ) (h : (b - 1) ^ 2 * (2 * b + 7) = 0) : b = 1 ∨ b = -7 / 2   :=  by sorry
