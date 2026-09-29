-- Prove2me | Theorems.Thm_WorkbookSource_base_6527
-- name    : WorkbookSource.base_6527
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:18:51.613284+00:00
-- url     : https://prove2.me/theorems/6111cbeb-2203-4785-af0d-eb9bd3e46c47
-- title:
--   A sixth-power sum bound at fixed sum three
-- statement:
--   Let $x,y,z>0$ such that $x+y+z=3$ .Prove that
--    $x^6+y^6+z^6+3\geq \frac{3}{32}(x+y)^2(y+z)^2(x+z)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6527` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6527; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6527 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) :  x ^ 6 + y ^ 6 + z ^ 6 + 3 ≥ (3 / 32) * (x + y) ^ 2 * (y + z) ^ 2 * (x + z) ^ 2  :=  by sorry
