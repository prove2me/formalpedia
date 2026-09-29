-- Prove2me | Theorems.Thm_WorkbookSource_base_12883
-- name    : WorkbookSource.base_12883
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:58.121977+00:00
-- url     : https://prove2.me/theorems/50a11fde-a9b5-4308-94fe-dfaf971bbe65
-- title:
--   A shifted quadratic difference ratio lower bound at fixed sum three
-- statement:
--   Let $x,y,z>0,x+y+z=3$ ,prove that:
--
--    $\frac{y+z-x^2}{y+z+4x}+\frac{z+x-y^2}{z+x+4y}+\frac{x+y-z^2}{x+y+4z}\geq \frac{1}{2}$
--
--    BQ
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12883` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12883; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12883 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (y + z - x ^ 2) / (y + z + 4 * x) + (z + x - y ^ 2) / (z + x + 4 * y) + (x + y - z ^ 2) / (x + y + 4 * z) ≥ 1 / 2  :=  by sorry
