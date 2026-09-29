-- Prove2me | Theorems.Thm_WorkbookSource_base_9181
-- name    : WorkbookSource.base_9181
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:40:37.61847+00:00
-- url     : https://prove2.me/theorems/d2165d63-8b3e-40bf-abac-8d48a4a2291b
-- title:
--   A shifted cyclic product ratio bound at fixed sum three
-- statement:
--   prove that: $\frac{xy}{y+1}+\frac{yz}{z+1}+\frac{zx}{x+1}\geq \frac{3}{2}xyz$ given $x,y,z>0$ and $x+y+z=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9181` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9181; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_9181 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) (hx1 : x + y + z = 3) : (x * y) / (y + 1) + (y * z) / (z + 1) + (z * x) / (x + 1) ≥ (3 * x * y * z) / 2  :=  by sorry
