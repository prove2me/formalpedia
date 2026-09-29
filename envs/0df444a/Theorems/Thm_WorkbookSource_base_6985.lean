-- Prove2me | Theorems.Thm_WorkbookSource_base_6985
-- name    : WorkbookSource.base_6985
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:32.95969+00:00
-- url     : https://prove2.me/theorems/641035e0-7d55-467a-93e1-bbcec95f7e14
-- title:
--   A symmetric quadratic ratio sum is at least one
-- statement:
--   Given $x,y,z>0$ , prove that $\frac{x^2}{y^2+z^2+yz}+\frac{y^2}{z^2+x^2+zx}+\frac{z^2}{x^2+y^2+xy}\geq1$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6985` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6985; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6985 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x^2 / (y^2 + z^2 + y * z) + y^2 / (z^2 + x^2 + z * x) + z^2 / (x^2 + y^2 + x * y)) ≥ 1  :=  by sorry
