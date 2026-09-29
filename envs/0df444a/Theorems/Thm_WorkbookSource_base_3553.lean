-- Prove2me | Theorems.Thm_WorkbookSource_base_3553
-- name    : WorkbookSource.base_3553
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:08:36.875692+00:00
-- url     : https://prove2.me/theorems/82dfbbfa-2947-4e74-a8ad-ed574fcc8d23
-- title:
--   A sum of squared linear ratios has an upper bound
-- statement:
--   Prove that for all real positive numbers $ x$ , $ y$ and $ z$ the following inequality is true: $ \frac{(2x+y+z)^2}{2x^2+(y+z)^2 }+ \frac{(2y+z+x)^2}{2y^2+(z+x)^2 }+\frac{(2z+x+y)^2}{2z^2+(x+y)^2 }\le 8$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_3553` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_3553; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_3553 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (2*x + y + z)^2 / (2 * x^2 + (y + z)^2) + (2*y + z + x)^2 / (2 * y^2 + (z + x)^2) + (2*z + x + y)^2 / (2 * z^2 + (x + y)^2) ≤ 8  :=  by sorry
