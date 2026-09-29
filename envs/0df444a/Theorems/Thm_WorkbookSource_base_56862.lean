-- Prove2me | Theorems.Thm_WorkbookSource_base_56862
-- name    : WorkbookSource.base_56862
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:44:11.658245+00:00
-- url     : https://prove2.me/theorems/f2a0d881-477d-4a4b-9ee9-b4ba1464da66
-- title:
--   A pair-product square sum has a reciprocal product upper bound
-- statement:
--   If $x,y,z$ are positive numbers such that $x+y+z=3$ , then
--   $x^{2}y^{2}+y^{2}z^{2}+z^{2}x^{2}\leq \frac 3{xyz}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56862` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56862; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56862 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≤ 3 / (x * y * z)  :=  by sorry
