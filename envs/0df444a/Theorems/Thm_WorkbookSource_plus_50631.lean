-- Prove2me | Theorems.Thm_WorkbookSource_plus_50631
-- name    : WorkbookSource.plus_50631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:38:13.698996+00:00
-- url     : https://prove2.me/theorems/b14a1581-1739-4be9-ab2d-0e86a14fd7c1
-- title:
--   A sixth-power bound for shifted linear products
-- statement:
--   Prove that for positive numbers \\( x, y, z \\), \\( 27(z + 2x + y)^6 \geq 1024(z + x)(x + y)(y + z + x)^3x \\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_50631` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_50631; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_50631 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 27 * (z + 2 * x + y) ^ 6 ≥ 1024 * (z + x) * (x + y) * (y + z + x) ^ 3 * x   :=  by sorry
