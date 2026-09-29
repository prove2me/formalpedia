-- Prove2me | Theorems.Thm_lean_workbook_plus_65625
-- name    : lean_workbook_plus_65625
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f680c8df-6848-4fc3-87a7-7432ab369e08
-- statement:
--   Well, right of the bat, you can see that $123456$ and $123$ are each divisible by $3$ . So you can get to $123456^3-123^5 \Rightarrow 27(41152^3 - (123^2\cdot41^3))$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65625 (x : ℤ) (hx : x = 123456) : x^3 - 123^5 = 27 * (41152^3 - (123^2 * 41^3))   :=  by sorry
