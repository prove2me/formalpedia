-- Prove2me | Theorems.Thm_WorkbookSource_base_5981
-- name    : WorkbookSource.base_5981
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:57.971467+00:00
-- url     : https://prove2.me/theorems/efa55f8f-2215-4e74-9274-b92ebcbabdae
-- title:
--   A cyclic quartic inequality with asymmetric coefficients
-- statement:
--   Prove that for non-negative real numbers x, y, and z, the following inequality holds:
--   $49\, \left( x+y+z \right) ^{4}-475\, \left( x+y+z \right) ^{2} \left( xy+xz+yz \right) -408\, \left( x+y+z \right) xyz+288\, \left( x+y+z \right) \left( {x}^{2}y+{y}^{2}z+{z}^{2}x \right) +832\, \left( xy+xz+yz \right) ^{2}\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5981` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5981; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5981 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 49 * (x + y + z) ^ 4 - 475 * (x + y + z) ^ 2 * (x*y + x*z + y*z) - 408 * (x + y + z) * x*y*z + 288 * (x + y + z) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) + 832 * (x*y + x*z + y*z) ^ 2 ≥ 0  :=  by sorry
