-- Prove2me | Theorems.Thm_lean_workbook_plus_17637
-- name    : lean_workbook_plus_17637
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/c33b42e6-5f75-438d-b290-22f2db8f6e70
-- statement:
--   Find the minimum value of $F(x,y)=\left | x-1 \right | + \left | x-2 \right | + \left | x-3 \right | + \left | x-4 \right | + \left | y-1 \right | + \left | y-2 \right | + \left | y-3 \right |$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17637 (x y : ℝ) : 6 ≤ abs (x - 1) + abs (x - 2) + abs (x - 3) + abs (x - 4) + abs (y - 1) + abs (y - 2) + abs (y - 3)   :=  by sorry
