-- Prove2me | Theorems.Thm_WorkbookSource_base_41666
-- name    : WorkbookSource.base_41666
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:00:48.28246+00:00
-- url     : https://prove2.me/theorems/c1fa9949-23a3-4a3a-a6ba-9898d09feef2
-- title:
--   A cyclic fourth-power reciprocal sum bounds a cubic product sum
-- statement:
--   Let $w,x,y,z$ be positive. Prove that
--    $$\frac{w^4}{z}+\frac{x^4}{w}+\frac{y^4}{x}+\frac{z^4}{y}\geq wz^2+xw^2+yx^2+zy^2 .$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41666` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41666; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41666 (w x y z : ℝ) (hw : 0 < w) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (w^4 / z + x^4 / w + y^4 / x + z^4 / y) ≥ w * z^2 + x * w^2 + y * x^2 + z * y^2  :=  by sorry
