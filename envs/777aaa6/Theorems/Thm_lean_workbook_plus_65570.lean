-- Prove2me | Theorems.Thm_lean_workbook_plus_65570
-- name    : lean_workbook_plus_65570
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/6d4b42b7-a843-4aea-971a-621c7ed03f66
-- statement:
--   And the answer is that (edited: )\n\n$\cos 2x = 1-2 \sin^{2}x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65570 (x : ℝ) : Real.cos (2 * x) = 1 - 2 * (Real.sin x)^2   :=  by sorry
