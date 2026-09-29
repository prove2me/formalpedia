-- Prove2me | Theorems.Thm_lean_workbook_plus_26895
-- name    : lean_workbook_plus_26895
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/e9dab293-4e36-44fe-bc1d-9378848834c5
-- statement:
--   Let $x,y,z \in R$ and $ x,y,z \not= 0$ and $\frac{1}{x}+\frac{1}{y}+\frac{1}{z}=0$ . Prove that: $\frac{yz}{x^2}+\frac{zx}{y^2}+\frac{xy}{z^2}=3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26895 (x y z : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0) (h : 1/x + 1/y + 1/z = 0) : y * z / x ^ 2 + z * x / y ^ 2 + x * y / z ^ 2 = 3   :=  by sorry
