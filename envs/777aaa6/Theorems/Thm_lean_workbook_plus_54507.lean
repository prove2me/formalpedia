-- Prove2me | Theorems.Thm_lean_workbook_plus_54507
-- name    : lean_workbook_plus_54507
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/8d44aca1-7076-428f-8da1-cbcbeb85d128
-- statement:
--   trying grouping the terms this way: $8x(xy-2) +48(xy-2)$ which yields $(8x+48)(xy-2)=\boxed{8(x+6)(xy-2)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54507 (x y : ℝ) : 8*x*(x*y - 2) + 48*(x*y - 2) = 8*(x + 6)*(x*y - 2)   :=  by sorry
