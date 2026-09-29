-- Prove2me | Theorems.Thm_lean_workbook_plus_56055
-- name    : lean_workbook_plus_56055
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/600c4a1a-eece-42ed-b8b7-55216ce84e91
-- statement:
--   Subtract first and third: \n\n $y(x-z) + (x-z) = -5 \Rightarrow (x-z)(y+1) = -5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56055 (x y z : ℝ) : y * (x - z) + (x - z) = -5 → (x - z) * (y + 1) = -5   :=  by sorry
