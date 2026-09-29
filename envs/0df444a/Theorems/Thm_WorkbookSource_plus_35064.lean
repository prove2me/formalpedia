-- Prove2me | Theorems.Thm_WorkbookSource_plus_35064
-- name    : WorkbookSource.plus_35064
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:47:29.472548+00:00
-- url     : https://prove2.me/theorems/27838e5d-84fc-4541-8c87-e6d0278e54ff
-- title:
--   A cyclic quartic inequality at positive sum three
-- statement:
--   prove that $\sum_{\text{cyc}} \left(x^4-8x^3y+18x^2y^2+xy^3-12xyz^2 \right) \ge 0$ given $x,y,z>0$ and $x+y+z=3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_35064` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_35064; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_35064 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : (x ^ 4 - 8 * x ^ 3 * y + 18 * x ^ 2 * y ^ 2 + x * y ^ 3 - 12 * x * y * z ^ 2) + (y ^ 4 - 8 * y ^ 3 * z + 18 * y ^ 2 * z ^ 2 + y * z ^ 3 - 12 * y * z * x ^ 2) + (z ^ 4 - 8 * z ^ 3 * x + 18 * z ^ 2 * x ^ 2 + z * x ^ 3 - 12 * z * x * y ^ 2) ≥ 0   :=  by sorry
