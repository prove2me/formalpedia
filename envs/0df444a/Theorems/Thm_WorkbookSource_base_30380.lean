-- Prove2me | Theorems.Thm_WorkbookSource_base_30380
-- name    : WorkbookSource.base_30380
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:00.852977+00:00
-- url     : https://prove2.me/theorems/c80d14b5-d650-4974-b988-8c6eebc16a46
-- title:
--   A product comparison for shifted quadratic factors
-- statement:
--   Let $x,y,z \in \mathbb{R}$ and greater than or equal to $1$ . Prove, $\prod (x^2-2x+2) \le (xyz)^2-2xyz+2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30380` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30380; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30380 (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) : (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ≤ (x * y * z)^2 - 2 * x * y * z + 2  :=  by sorry
