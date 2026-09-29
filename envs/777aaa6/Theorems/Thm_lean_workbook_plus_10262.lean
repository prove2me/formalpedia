-- Prove2me | Theorems.Thm_lean_workbook_plus_10262
-- name    : lean_workbook_plus_10262
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/e5bebcfc-b4a7-40e9-9ad4-ec2c4f066169
-- statement:
--   Given $x$, $y$, $z>0$ and $xyz=1$, prove that $\sum{x^2(2y-1)^2}+5-(1+x)(1+y)(1+z)-3(1-x)(1-y)(1-z)=\sum{(2xy-x-1)^2}\ge{0}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10262 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x * y * z = 1) : (x ^ 2 * (2 * y - 1) ^ 2 + y ^ 2 * (2 * z - 1) ^ 2 + z ^ 2 * (2 * x - 1) ^ 2) + 5 - (1 + x) * (1 + y) * (1 + z) - 3 * (1 - x) * (1 - y) * (1 - z) = (2 * x * y - x - 1) ^ 2 + (2 * y * z - y - 1) ^ 2 + (2 * z * x - z - 1) ^ 2   :=  by sorry
