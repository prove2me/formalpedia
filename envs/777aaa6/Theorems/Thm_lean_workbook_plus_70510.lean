-- Prove2me | Theorems.Thm_lean_workbook_plus_70510
-- name    : lean_workbook_plus_70510
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/995317ca-c7c3-4fc1-995f-d79d80dbbadb
-- statement:
--   Given $x = 9/2$ and $y = 1/2$, calculate $1/x + 1/y$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70510 (x y : ℚ) (hx : x = 9/2) (hy : y = 1/2) : 1/x + 1/y = 20/9   :=  by sorry
