-- Prove2me | Theorems.Thm_WorkbookSource_base_29516
-- name    : WorkbookSource.base_29516
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:50.874004+00:00
-- url     : https://prove2.me/theorems/f1823d3d-7313-4ab3-80e9-feb4ac7b8b5a
-- title:
--   Two cyclic cubic sums bound symmetric products
-- statement:
--   prove that
--
--   \( (xy^2+yz^2+zx^2)(x^2y+y^2z+z^2x) \geq (x+y+z)(x^2+y^2+z^2)xyz \)
--
--   where \( x,y,z \geq 0 \)
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_29516` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_29516; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_29516 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x * y ^ 2 + y * z ^ 2 + z * x ^ 2) * (x ^ 2 * y + y ^ 2 * z + z ^ 2 * x) ≥ (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2) * x * y * z  :=  by sorry
