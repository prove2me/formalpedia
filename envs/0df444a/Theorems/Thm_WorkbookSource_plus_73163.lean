-- Prove2me | Theorems.Thm_WorkbookSource_plus_73163
-- name    : WorkbookSource.plus_73163
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:53:36.260935+00:00
-- url     : https://prove2.me/theorems/3e19f351-b004-4f7a-ab96-647cfd27bf59
-- title:
--   A weighted quadratic pair-product ratio sum is at most one half
-- statement:
--   Prove that if $ x,y,z>0$ then $ \frac{xy}{3x^2+2y^2+z^2}+\frac{yz}{3y^2+2z^2+x^2}+\frac{zx}{3z^2+2x^2+y^2} \leq \frac{1}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_73163` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_73163; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_73163 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x * y / (3 * x ^ 2 + 2 * y ^ 2 + z ^ 2) + y * z / (3 * y ^ 2 + 2 * z ^ 2 + x ^ 2) + z * x / (3 * z ^ 2 + 2 * x ^ 2 + y ^ 2)) ≤ 1 / 2   :=  by sorry
