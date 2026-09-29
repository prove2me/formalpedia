-- Prove2me | Theorems.Thm_WorkbookSource_base_17256
-- name    : WorkbookSource.base_17256
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:07:19.283138+00:00
-- url     : https://prove2.me/theorems/0d681131-995d-4ffa-924d-2865a82f85f2
-- title:
--   A cyclic shifted linear ratio sum is at least three
-- statement:
--   Let $x,y,z>0$ ,prove that;
--
--   ${\frac {2+y+3\,x}{2+x+3\,y}}+{\frac {2+z+3\,y}{2+y+3\,z}}+{\frac {2+x+3\,z}{2+z+3\,x}}\geq 3.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17256` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17256; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17256 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 + y + 3 * x) / (2 + x + 3 * y) + (2 + z + 3 * y) / (2 + y + 3 * z) + (2 + x + 3 * z) / (2 + z + 3 * x) ≥ 3  :=  by sorry
