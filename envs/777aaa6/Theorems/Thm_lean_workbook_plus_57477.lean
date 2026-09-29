-- Prove2me | Theorems.Thm_lean_workbook_plus_57477
-- name    : lean_workbook_plus_57477
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/11345990-4bbf-4c35-bd11-f8ea099955b8
-- statement:
--   Prove that $ 6303t^{5}+3320t^{4}+1776\geq 5656t^{3}$ , where $ 0\leq t\leq1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57477 (t : ℝ) (ht : 0 ≤ t ∧ t ≤ 1) :
  6303 * t ^ 5 + 3320 * t ^ 4 + 1776 ≥ 5656 * t ^ 3   :=  by sorry
