-- Prove2me | Theorems.Thm_lean_workbook_plus_79029
-- name    : lean_workbook_plus_79029
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/746c7fed-267f-4994-b622-78eae8ad70dd
-- statement:
--   Prove that $x-1 \geq \ln x$ for $x>0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79029 (x : ℝ) (hx : 0 < x) : x - 1 ≥ Real.log x   :=  by sorry
