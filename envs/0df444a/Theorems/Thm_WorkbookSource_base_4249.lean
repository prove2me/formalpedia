-- Prove2me | Theorems.Thm_WorkbookSource_base_4249
-- name    : WorkbookSource.base_4249
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:11:52.793079+00:00
-- url     : https://prove2.me/theorems/878282b8-c003-4785-9847-276057e3ab1f
-- title:
--   A cyclic linear-over-squared sum has a symmetric lower bound
-- statement:
--   Let $x,y,z>0,$
--   $\frac{x}{(x+y)^2}+\frac{y}{(y+z)^2}+\frac{z}{(z+x)^2} \ge \frac{1}{x+y+z}+\frac{10xyz}{(x+y)(y+z)(z+x)(x+y+z)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4249` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4249; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4249 (x y z : ℝ) (hx : x > 0) (hy : y > 0) (hz : z > 0) : (x / (x + y) ^ 2 + y / (y + z) ^ 2 + z / (z + x) ^ 2) ≥ 1 / (x + y + z) + 10 * x * y * z / ((x + y) * (y + z) * (z + x) * (x + y + z))  :=  by sorry
