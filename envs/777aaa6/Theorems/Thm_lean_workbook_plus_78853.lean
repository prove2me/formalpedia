-- Prove2me | Theorems.Thm_lean_workbook_plus_78853
-- name    : lean_workbook_plus_78853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/fcaadf5e-6a19-44ae-860a-ed7fc75fae67
-- statement:
--   where $ \phi(x)=x- [x] - \frac12$ (so it can be bound by 1/2)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78853 (x : ℝ) : |x - ⌊x⌋ - 1 / 2| ≤ 1 / 2   :=  by sorry
