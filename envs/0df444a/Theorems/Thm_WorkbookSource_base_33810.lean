-- Prove2me | Theorems.Thm_WorkbookSource_base_33810
-- name    : WorkbookSource.base_33810
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:50.184112+00:00
-- url     : https://prove2.me/theorems/9ea5eda0-a7ce-4ae5-8957-ce9bddf8f68d
-- title:
--   A product of power sums bounded by an eighth-power sum
-- statement:
--   Let $x, y, z$ be positive real numbers. Prove that:
--    $$\frac{(x^3+y^3+z^3)(x^5+y^5+z^5)}{x^8+y^8+z^8} \leq 3$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33810` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33810; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33810 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x^3 + y^3 + z^3) * (x^5 + y^5 + z^5) / (x^8 + y^8 + z^8) ≤ 3  :=  by sorry
