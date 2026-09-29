-- Prove2me | Theorems.Thm_lean_workbook_plus_70629
-- name    : lean_workbook_plus_70629
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/7111d9cd-41f6-47e0-bb07-30ab22e9f6e1
-- statement:
--   Prove that for $ x\in [0,1] $ $1-x\leq e^{-x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70629 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) : 1 - x ≤ exp (- x)   :=  by sorry
