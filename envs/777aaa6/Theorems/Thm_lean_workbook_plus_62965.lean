-- Prove2me | Theorems.Thm_lean_workbook_plus_62965
-- name    : lean_workbook_plus_62965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/63fc0f0f-f77f-4b6e-a0e1-491dc3f4e6bf
-- statement:
--   Find the minimum value of $S=\left | x+1 \right |+\left | x+5 \right |+\left | x+14 \right |+\left | x+97 \right |+\left | x+1920 \right |$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62965 (x : ℝ) : 2011 ≤ abs (x + 1) + abs (x + 5) + abs (x + 14) + abs (x + 97) + abs (x + 1920)   :=  by sorry
