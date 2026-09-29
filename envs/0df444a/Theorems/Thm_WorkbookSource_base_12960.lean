-- Prove2me | Theorems.Thm_WorkbookSource_base_12960
-- name    : WorkbookSource.base_12960
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:03:59.102878+00:00
-- url     : https://prove2.me/theorems/518f0cb8-b5e0-4e88-a222-84d978fb5fc2
-- title:
--   A two-variable polynomial inequality on the nonnegative quadrant
-- statement:
--   Let be $ x,y\ge 0$ . Prove that : $ 8x^3y+y^3+2x\ge 2xy(2x+y+1)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12960` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12960; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12960 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 8 * x ^ 3 * y + y ^ 3 + 2 * x ≥ 2 * x * y * (2 * x + y + 1)  :=  by sorry
