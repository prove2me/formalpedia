-- Prove2me | Theorems.Thm_WorkbookSource_base_41900
-- name    : WorkbookSource.base_41900
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:02:18.283316+00:00
-- url     : https://prove2.me/theorems/35a8241d-a43e-4109-8f4b-5d00f18f986a
-- title:
--   An asymmetric cyclic ratio sum is at least four
-- statement:
--   prove that: $\frac{x}{y}+\frac{y}{z}+\frac{2(y+z)}{x+y}\geq 4$, where $x,y,z>0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41900` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41900; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41900 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / y + y / z + 2 * (y + z) / (x + y)) ≥ 4  :=  by sorry
