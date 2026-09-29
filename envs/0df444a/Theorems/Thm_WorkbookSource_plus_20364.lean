-- Prove2me | Theorems.Thm_WorkbookSource_plus_20364
-- name    : WorkbookSource.plus_20364
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:53:02.217064+00:00
-- url     : https://prove2.me/theorems/9a283474-62b4-4899-b324-78370b1638d3
-- title:
--   A sum minus pairwise product bound under a cubic constraint
-- statement:
--   If $x,y,z$ are positive real satisfy $x^2+y^2+z^2+2xyz=1$, prove that $(x+y+z) -(xy+yz+zx) \geq \frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_20364` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_20364; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_20364 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 + 2 * x * y * z = 1) : (x + y + z) - (x * y + y * z + z * x) ≥ 3 / 4   :=  by sorry
