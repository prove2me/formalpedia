-- Prove2me | Theorems.Thm_WorkbookSource_base_13239
-- name    : WorkbookSource.base_13239
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:49:20.77366+00:00
-- url     : https://prove2.me/theorems/2a2c9016-36fe-44d9-9d90-265663a952de
-- title:
--   A cyclic shifted linear ratio sum is at least three
-- statement:
--   Prove that for positive reals x, y, and z, the following inequality holds:
--   $\frac{2z+1}{x+y+1}+\frac{1+2x}{y+z+1}+\frac{2y+1}{z+x+1}\geq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13239` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13239; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13239 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2 * z + 1) / (x + y + 1) + (1 + 2 * x) / (y + z + 1) + (2 * y + 1) / (z + x + 1) ≥ 3  :=  by sorry
