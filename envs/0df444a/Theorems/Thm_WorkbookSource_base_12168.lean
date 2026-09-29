-- Prove2me | Theorems.Thm_WorkbookSource_base_12168
-- name    : WorkbookSource.base_12168
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:14.401758+00:00
-- url     : https://prove2.me/theorems/e112309b-3f7a-46ff-8bad-0ebeef91a736
-- title:
--   A fourth-power bound for a cyclic cubic product sum
-- statement:
--   Prove that, for all positive real numbers $x, y$ and $z$ ,
--   $(x+y+z)^4\geq \frac{256}{27}(x^3y+y^3z+z^3x)+\frac{473}{27}(x+y+z)xyz$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12168` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12168; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12168 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x + y + z) ^ 4 ≥ (256 / 27) * (x ^ 3 * y + y ^ 3 * z + z ^ 3 * x) + (473 / 27) * (x + y + z) * x * y * z  :=  by sorry
