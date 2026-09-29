-- Prove2me | Theorems.Thm_lean_workbook_plus_2
-- name    : lean_workbook_plus_2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a8891c1f-08c6-4767-9650-11d461d5173f
-- statement:
--   Solve for $x$ in the given inequality: $x^2-2x-24<0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2 (x : ℝ) : x^2 - 2*x - 24 < 0 ↔ x ∈ Set.Ioo (-4) 6   :=  by sorry
