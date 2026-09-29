-- Prove2me | Theorems.Thm_lean_workbook_plus_81452
-- name    : lean_workbook_plus_81452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7d087e96-c2a6-4ee6-b960-67678e87d571
-- statement:
--   Prove that $\\dbinom{n+1}{3}-\\dbinom{n-1}{3}=(n-1)^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81452 (n : ℕ) : (n + 1).choose 3 - (n - 1).choose 3 = (n - 1)^2   :=  by sorry
