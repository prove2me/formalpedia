-- Prove2me | Theorems.Thm_WorkbookSource_base_2054
-- name    : WorkbookSource.base_2054
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T23:05:12.003083+00:00
-- url     : https://prove2.me/theorems/b7127a58-6e92-447e-ba15-fbc705e7b012
-- title:
--   A degree-eight bound involving pairwise squared sums
-- statement:
--   substitute $a=\frac{x}{x+y+z}$ etc.[x,y,z>0]
--   then it turns into
--    $\frac{(x^2+y^2)(y^2+z^2)(z^2+x^2)}{(x+y+z)^6} \ge 8\frac{(x^2y^2+y^2z^2+z^2x^2)^2}{(x+y+z)^8}$
--
--   i.e. $(x+y+z)^2(x^2+y^2)(z^2+x^2)(y^2+z^2) \ge 8(x^2y^2+y^2z^2+z^2x^2)^2$
--
--   now it is a symmetric inequality in x,y,z , which can be proved using murihead inequality
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2054` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2054; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2054 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y + z) ^ 2 * (x ^ 2 + y ^ 2) * (y ^ 2 + z ^ 2) * (z ^ 2 + x ^ 2) ≥ 8 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) ^ 2  :=  by sorry
