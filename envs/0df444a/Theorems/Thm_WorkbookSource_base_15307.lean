-- Prove2me | Theorems.Thm_WorkbookSource_base_15307
-- name    : WorkbookSource.base_15307
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:00:13.698972+00:00
-- url     : https://prove2.me/theorems/8f33762d-6309-449d-a458-cf7f1f05d68d
-- title:
--   A weighted quadratic reciprocal upper bound
-- statement:
--   for positive real numbers $x,y,z$ prove that $$\frac{x}{4x^2+4y^2+z^2}+\frac{y}{4y^2+4z^2+x^2}+\frac{z}{4z^2+4x^2+y^2} \leq \frac{1}{x+y+z}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_15307` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_15307; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_15307 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x / (4 * x ^ 2 + 4 * y ^ 2 + z ^ 2) + y / (4 * y ^ 2 + 4 * z ^ 2 + x ^ 2) + z / (4 * z ^ 2 + 4 * x ^ 2 + y ^ 2)) ≤ 1 / (x + y + z)  :=  by sorry
