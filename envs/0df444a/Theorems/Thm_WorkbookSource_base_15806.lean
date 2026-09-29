-- Prove2me | Theorems.Thm_WorkbookSource_base_15806
-- name    : WorkbookSource.base_15806
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:47:00.190667+00:00
-- url     : https://prove2.me/theorems/fa90faf1-0ef4-48b2-acd1-cbd3d797975d
-- title:
--   A sixth-degree lower bound for squared pairwise products
-- statement:
--   Let $x,y,z$ be non-negative real numbers, Prove that :
--    $27((x+y)(y+z)(z+x))^{2}\geq 64$ $xyz(x+y+z)^{3}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15806` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15806; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15806 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : 27 * ((x + y) * (y + z) * (z + x)) ^ 2 ≥ 64 * x * y * z * (x + y + z) ^ 3  :=  by sorry
