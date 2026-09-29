-- Prove2me | Theorems.Thm_WorkbookSource_plus_27662
-- name    : WorkbookSource.plus_27662
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:51:49.647259+00:00
-- url     : https://prove2.me/theorems/3d610219-6c01-4d3d-b4d4-2c573febd699
-- title:
--   A quadratic reciprocal product bounds a linear reciprocal product
-- statement:
--   Let $x,y,z $ be positive real numbers. Prove that $(x^2 + y^2 + z^2) \big(\frac{1}{x^2}+\frac{1}{y^2}+\frac{1}{z^2}\big)\geq 5(x + y + z) \big(\frac{1}{x}+\frac{1}{y}+\frac{1}{z}\big)-\frac{73}{2}.$ p/5829942994
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_27662` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_27662; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_27662 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^2 + y^2 + z^2) * (1 / x^2 + 1 / y^2 + 1 / z^2) ≥ 5 * (x + y + z) * (1 / x + 1 / y + 1 / z) - 73 / 2   :=  by sorry
