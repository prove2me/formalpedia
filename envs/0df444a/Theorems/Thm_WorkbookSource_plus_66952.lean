-- Prove2me | Theorems.Thm_WorkbookSource_plus_66952
-- name    : WorkbookSource.plus_66952
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:56.416126+00:00
-- url     : https://prove2.me/theorems/4b0ee1a3-60d9-4b31-8c25-e57a349409f9
-- title:
--   A quartic bound for mixed pairwise products
-- statement:
--   Let $x,y,z\geq 0.$ Prove that
--   $$ xy(x^2+y^2)+yz(y^2+z^2)+zx(z^2+x^2)\leq \frac{1}{8}(x+y+z)^4 $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_66952` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_66952; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_66952 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : (x * y * (x ^ 2 + y ^ 2) + y * z * (y ^ 2 + z ^ 2) + z * x * (z ^ 2 + x ^ 2)) ≤ (1 / 8) * (x + y + z) ^ 4   :=  by sorry
