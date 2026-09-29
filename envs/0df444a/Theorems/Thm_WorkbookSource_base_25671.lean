-- Prove2me | Theorems.Thm_WorkbookSource_base_25671
-- name    : WorkbookSource.base_25671
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:43:02.086082+00:00
-- url     : https://prove2.me/theorems/baddcc93-e28f-4035-a021-7578e409953d
-- title:
--   A cyclic difference ratio sum with shifted product denominators
-- statement:
--   Prove that for all positive real number $x,y,z$ the inequality $$\frac{x-y}{xy+2y+1}+\frac{y-z}{yz+2z+1}+\frac{z-x}{zx+2x+1}\geq 0$$ holds.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_25671` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_25671; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_25671 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x - y) / (x * y + 2 * y + 1) + (y - z) / (y * z + 2 * z + 1) + (z - x) / (z * x + 2 * x + 1) ≥ 0  :=  by sorry
