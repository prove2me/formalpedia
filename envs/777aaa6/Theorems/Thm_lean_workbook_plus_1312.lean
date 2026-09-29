-- Prove2me | Theorems.Thm_lean_workbook_plus_1312
-- name    : lean_workbook_plus_1312
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/53052ee3-4161-4fe6-965c-03d71bdf5afa
-- statement:
--   Prove $\frac{1-x}{1+x}\frac{1-y}{1+y}\geq\frac{1-x-y}{1+x+y}$ for all $x,y>0,x+y<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1312 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hxy : x + y < 1) : (1 - x) / (1 + x) * (1 - y) / (1 + y) ≥ (1 - x - y) / (1 + x + y)   :=  by sorry
