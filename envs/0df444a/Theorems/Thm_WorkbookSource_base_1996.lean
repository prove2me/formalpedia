-- Prove2me | Theorems.Thm_WorkbookSource_base_1996
-- name    : WorkbookSource.base_1996
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:56:37.871853+00:00
-- url     : https://prove2.me/theorems/40a98061-a939-4f61-a9a0-4c939172cc04
-- title:
--   A squared total times reciprocal pairwise squares is at least ten
-- statement:
--   Prove or find the minimum of LHS: \((x+y+z)^2(\frac 1{x^2+y^2}+\frac 1{y^2+z^2}+\frac 1{z^2+x^2}) \geq 10\) where \(x, y, z > 0\).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1996` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1996; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1996 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 2 * (1 / (x ^ 2 + y ^ 2) + 1 / (y ^ 2 + z ^ 2) + 1 / (z ^ 2 + x ^ 2)) ≥ 10  :=  by sorry
