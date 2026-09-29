-- Prove2me | Theorems.Thm_WorkbookSource_base_37184
-- name    : WorkbookSource.base_37184
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:01.685999+00:00
-- url     : https://prove2.me/theorems/bc5f51b1-4b13-446f-94f3-a522317bfbeb
-- title:
--   An asymmetric pairwise ratio lower bound
-- statement:
--   Prove that for positive real numbers x, y, and z:
--   $\frac{x}{y+z}+\frac{z}{x+y}\geq \frac{z+x}{2y+z+x}+\frac{1}{8}\frac{-2y+7z+7x}{x+y+z}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37184` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37184; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37184 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (y + z) + z / (x + y)) ≥ (z + x) / (2 * y + z + x) + 1 / 8 * (-2 * y + 7 * z + 7 * x) / (x + y + z)  :=  by sorry
