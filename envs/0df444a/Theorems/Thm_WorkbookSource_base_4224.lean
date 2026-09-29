-- Prove2me | Theorems.Thm_WorkbookSource_base_4224
-- name    : WorkbookSource.base_4224
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:19.390666+00:00
-- url     : https://prove2.me/theorems/515bec54-836d-4838-96ca-c6f2066d6b92
-- title:
--   An asymmetric pairwise ratio sum has a lower bound
-- statement:
--   x,y,z>0,prove that:
--
--    $\frac{x}{y+z}+\frac{2y}{z+x}+\frac{2z}{x+y}+\frac{x}{x+y}\geq \frac{5}{2}+\frac{z}{z+x}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4224` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4224; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4224 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + 2 * y / (z + x) + 2 * z / (x + y) + x / (x + y)) ≥ 5 / 2 + z / (z + x)  :=  by sorry
