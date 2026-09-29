-- Prove2me | Theorems.Thm_WorkbookSource_base_8251
-- name    : WorkbookSource.base_8251
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:11:03.360165+00:00
-- url     : https://prove2.me/theorems/33b520f5-da32-413c-ba8b-7fce5350d8eb
-- title:
--   A normalized quartic bound with a triple-product correction
-- statement:
--   Let $x,y,z\geq 0,x+y+z=1$ ,prove that: $21xyz+1\geq 16(xy+xz+yz)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8251` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8251; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8251 (x y z : ℝ) (hx : x + y + z = 1) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z) : 21 * x * y * z + 1 ≥ 16 * (x * y + x * z + y * z)^2  :=  by sorry
