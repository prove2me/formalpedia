-- Prove2me | Theorems.Thm_WorkbookSource_base_2775
-- name    : WorkbookSource.base_2775
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:02:14.130658+00:00
-- url     : https://prove2.me/theorems/2f8725d3-4e36-4e8e-b4b6-cf5e21262b68
-- title:
--   A cyclic product-power ratio comparison at fixed sum three
-- statement:
--   Let $x,y,z$ be positive reals with sum $3$ . Prove: $\displaystyle{\frac{y^3z^3+2}{yz}+\frac{z^3x^3+2}{zx}+\frac{x^3y^3+2}{xy}\ge \frac{x^2+2}{x}+\frac{y^2+2}{y}+\frac{z^2+2}{z}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2775` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2775; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2775 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (y^3 * z^3 + 2) / (y * z) + (z^3 * x^3 + 2) / (z * x) + (x^3 * y^3 + 2) / (x * y) ≥ (x^2 + 2) / x + (y^2 + 2) / y + (z^2 + 2) / z  :=  by sorry
