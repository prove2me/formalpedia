-- Prove2me | Theorems.Thm_lean_workbook_plus_9408
-- name    : lean_workbook_plus_9408
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ddc40de1-4754-47b3-a386-987cf13ed947
-- statement:
--   Solve: $ x^{\log _{x} 30}=30$ with $ x>0$ and $ x\neq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9408 (x : ℝ) (hx : x > 0 ∧ x ≠ 1) : x^((Real.log 30) / (Real.log x)) = 30   :=  by sorry
