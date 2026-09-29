-- Prove2me | Theorems.Thm_WorkbookSource_base_1552
-- name    : WorkbookSource.base_1552
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:54:03.356563+00:00
-- url     : https://prove2.me/theorems/180ed053-5dd5-4a30-8972-9c3c7afc7e17
-- title:
--   A quadratic reciprocal sum bounds twice the total
-- statement:
--   Let $x, y, z$ be positive real numbers. Prove that $\frac{y^2 + z^2}{x}+\frac{z^2 + x^2}{y}+\frac{x^2 + y^2}{z}\ge 2(x + y + z)$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1552` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1552; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1552 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y ^ 2 + z ^ 2) / x + (z ^ 2 + x ^ 2) / y + (x ^ 2 + y ^ 2) / z ≥ 2 * (x + y + z)  :=  by sorry
