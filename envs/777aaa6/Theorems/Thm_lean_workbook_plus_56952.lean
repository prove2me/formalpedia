-- Prove2me | Theorems.Thm_lean_workbook_plus_56952
-- name    : lean_workbook_plus_56952
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4647264e-3a34-4b43-9222-488c0ecf10dc
-- statement:
--   For $x\ge 1$ : $\log_2x\log_2(x+1)+1\ge 1>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56952 (x : ℝ) (hx : 1 ≤ x) : Real.logb 2 x * Real.logb 2 (x + 1) + 1 ≥ 1 ∧ 1 > 0   :=  by sorry
