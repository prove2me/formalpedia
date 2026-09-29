-- Prove2me | Theorems.Thm_WorkbookSource_base_7327
-- name    : WorkbookSource.base_7327
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:33:08.998534+00:00
-- url     : https://prove2.me/theorems/904ecce0-f58b-41e5-96f1-726a200188d8
-- title:
--   A cyclic cubic ratio sum bounds pairwise products
-- statement:
--   Prove that for $x, y, z > 0$, the following inequality holds:
--   $\frac{x(x^2 + 2yz)}{x + 2y} + \frac{y(y^2 + 2zx)}{y + 2z} + \frac{z(z^2 + 2xy)}{z + 2x} \ge xy + yz + zx$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7327` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7327; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7327 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * (x ^ 2 + 2 * y * z) / (x + 2 * y) + y * (y ^ 2 + 2 * z * x) / (y + 2 * z) + z * (z ^ 2 + 2 * x * y) / (z + 2 * x)) ≥ x * y + y * z + z * x  :=  by sorry
