-- Prove2me | Theorems.Thm_lean_workbook_plus_61371
-- name    : lean_workbook_plus_61371
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/ffd2da9d-51d7-49b7-8896-4299d3f3d758
-- statement:
--   For $n=3$ : $2^2+3^2+13^2+17^2+23^2=1000$ (and some others)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61371 (hx: A = ({2, 3, 13, 17, 23})) : ∑ i in A, i^2 = 1000   :=  by sorry
