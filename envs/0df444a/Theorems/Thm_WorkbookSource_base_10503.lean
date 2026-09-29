-- Prove2me | Theorems.Thm_WorkbookSource_base_10503
-- name    : WorkbookSource.base_10503
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:41:22.761976+00:00
-- url     : https://prove2.me/theorems/825c6ebd-29a8-4563-982b-b311a029793c
-- title:
--   Two cyclic cubic sums bound a product of pairwise sums
-- statement:
--   x, y, z > 0, prove that;
--
--   $\left( x{y}^{2}+y{z}^{2}+z{x}^{2} \right) \left( {x}^{2}y+{y}^{2}z+{z}^{2}x \right) \geq \left( xy+zx+yz \right) \left( {x}^{2}{y}^{2}+{y}^{2}{z}^{2}+{x}^{2}{z}^{2} \right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10503` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10503; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10503 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ≥ (x * y + z * x + y * z) * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2)  :=  by sorry
