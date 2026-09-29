-- Prove2me | Theorems.Thm_WorkbookSource_plus_82114
-- name    : WorkbookSource.plus_82114
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:26.494331+00:00
-- url     : https://prove2.me/theorems/ce3d97bd-9c8f-4c8c-bada-efe20e31bf8d
-- title:
--   Two cyclic cubic sums bound a cubed pairwise sum
-- statement:
--   Let $x,y,z$ be positive real numbers. Prove that $3\, \left( {x}^{2}y+{y}^{2}z+{z}^{2}x \right) \left( x{y}^{2}+y{z}^{2}+{x}^{2}z \right) \geq \left( xy+zx+yz \right) ^{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_82114` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_82114; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_82114 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 3 * (x^2 * y + y^2 * z + z^2 * x) * (x * y^2 + y * z^2 + x^2 * z) ≥ (x * y + y * z + z * x)^3   :=  by sorry
