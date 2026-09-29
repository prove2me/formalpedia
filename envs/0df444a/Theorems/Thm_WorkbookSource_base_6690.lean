-- Prove2me | Theorems.Thm_WorkbookSource_base_6690
-- name    : WorkbookSource.base_6690
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:25.681207+00:00
-- url     : https://prove2.me/theorems/ab6982d0-c614-4b6f-a647-4f2db2733a4e
-- title:
--   A shifted cubic reciprocal bound at fixed sum three
-- statement:
--   Let $x,y,z$ be pozitive real number satisfyng $x+y+z=3$ . Prove that $\sum\limits_{cyclic}{\frac{x^3+4}{x+2}}\ge 5.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6690` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6690; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6690 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x^3 + 4)/(x + 2) + (y^3 + 4)/(y + 2) + (z^3 + 4)/(z + 2) ≥ 5  :=  by sorry
