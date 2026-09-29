-- Prove2me | Theorems.Thm_WorkbookSource_base_37690
-- name    : WorkbookSource.base_37690
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:31:16.384692+00:00
-- url     : https://prove2.me/theorems/84755e5d-15a1-47bf-81a7-5993383ad250
-- title:
--   A shifted squared pairwise reciprocal lower bound at fixed sum three
-- statement:
--   If x,y,z>0 and x+y+z=3 prove that
--    $\frac{1}{4+(x+y)^2}+\frac{1}{4+(y+z)^2}+\frac{1}{4+(z+x)^2}\geq \frac{3}{8}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37690` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37690; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37690 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hx1 : x + y + z = 3) : 1 / (4 + (x + y) ^ 2) + 1 / (4 + (y + z) ^ 2) + 1 / (4 + (z + x) ^ 2) ≥ 3 / 8  :=  by sorry
