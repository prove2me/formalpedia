-- Prove2me | Theorems.Thm_lean_workbook_plus_46074
-- name    : lean_workbook_plus_46074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e0c227c7-f0d3-46e6-a066-8f388064150c
-- statement:
--   From $|z-3+i|=3$ we get $(x-3)^2+(y+1)^2=9,$ or $x^2+y^2-6x+2y+1=0.\ (2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46074 (x y : ℝ) (h₁ : (x - 3) ^ 2 + (y + 1) ^ 2 = 9) : x ^ 2 + y ^ 2 - 6 * x + 2 * y + 1 = 0   :=  by sorry
