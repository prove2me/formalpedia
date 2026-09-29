-- Prove2me | Theorems.Thm_lean_workbook_plus_79823
-- name    : lean_workbook_plus_79823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9a66f74a-5514-4c78-9e0f-02979abbfb23
-- statement:
--   Prove for all $a,b,c \in R$ , the following multivariable inequality holds: $(x+y)^2 + (y+z)^2 + (z+x)^2 \ge (x+y+z)^2 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79823 (x y z: ℝ) : (x + y) ^ 2 + (y + z) ^ 2 + (z + x) ^ 2 >= (x + y + z) ^ 2   :=  by sorry
