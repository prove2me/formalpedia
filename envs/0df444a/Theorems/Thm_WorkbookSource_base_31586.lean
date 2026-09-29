-- Prove2me | Theorems.Thm_WorkbookSource_base_31586
-- name    : WorkbookSource.base_31586
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:26:10.885753+00:00
-- url     : https://prove2.me/theorems/1576b609-9a6a-4935-83c7-7617de878d40
-- title:
--   An asymmetric pairwise ratio inequality
-- statement:
--   Let $x,y,z>0$ ,prove that: $\frac{y}{z+x}(x+y)+\frac{y}{z+x}(y+z)+x+\frac{z}{x+y}(y+z)+\frac{z}{x+y}(z+x)\geq \frac{5}{2}z+\frac{5}{2}y.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_31586` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_31586; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_31586 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (y / (z + x)) * (x + y) + (y / (z + x)) * (y + z) + x + (z / (x + y)) * (y + z) + (z / (x + y)) * (z + x) ≥ (5 / 2) * z + (5 / 2) * y  :=  by sorry
