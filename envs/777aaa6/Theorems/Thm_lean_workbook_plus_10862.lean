-- Prove2me | Theorems.Thm_lean_workbook_plus_10862
-- name    : lean_workbook_plus_10862
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/38b70d85-434c-417b-9150-2c231dff6ef3
-- statement:
--   For $ x,y,z$ positive real numbers, prove that $(2x - y - z)\cdot\frac {x + y}{y + z} + (2y - z - x)\cdot\frac {y + z}{z + x} + (2z - x - y)\cdot\frac {z + x}{x + y}\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10862 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2*x - y - z)*(x + y)/(y + z) + (2*y - z - x)*(y + z)/(z + x) + (2*z - x - y)*(z + x)/(x + y) ≥ 0   :=  by sorry
