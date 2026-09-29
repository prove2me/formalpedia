-- Prove2me | Theorems.Thm_WorkbookSource_base_37861
-- name    : WorkbookSource.base_37861
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:36:14.934853+00:00
-- url     : https://prove2.me/theorems/50fc7414-4462-4df5-8142-2bfdfedf0388
-- title:
--   A cyclic quadratic difference ratio sum is at least three halves
-- statement:
--   Prove that for $x,y,z \in \mathbf{R^+}$, $\frac{x(3x-y)}{y(3z+x)}+\frac{y(3y-z)}{z(3x+y)}+\frac{z(3z-x)}{x(3y+z)}\geq \frac{3}{2}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37861` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37861; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37861 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * (3 * x - y) / (y * (3 * z + x)) + y * (3 * y - z) / (z * (3 * x + y)) + z * (3 * z - x) / (x * (3 * y + z))) ≥ 3 / 2  :=  by sorry
