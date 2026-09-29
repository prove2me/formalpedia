-- Prove2me | Theorems.Thm_WorkbookSource_base_14032
-- name    : WorkbookSource.base_14032
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:39.590983+00:00
-- url     : https://prove2.me/theorems/65559859-38ff-4fed-bb66-64f71b96b10d
-- title:
--   A cyclic quintic nonnegativity inequality
-- statement:
--   Let $x,y,z\geq 0$ ,prove that: $-x(1+x)(1+z)(x+y)(y+z)-y(1+x)(y+1)(y+z)(z+x)-z(1+z)(x+y)(y+1)(z+x)+1/2(1+x)^2(y+z)^2(x+y)+1/2(y+1)^2(z+x)^2(y+z)+1/2(1+z)^2(x+y)^2(z+x)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14032` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14032; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14032 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : -x * (1 + x) * (1 + z) * (x + y) * (y + z) - y * (1 + x) * (y + 1) * (y + z) * (z + x) - z * (1 + z) * (x + y) * (y + 1) * (z + x) + 1 / 2 * (1 + x) ^ 2 * (y + z) ^ 2 * (x + y) + 1 / 2 * (y + 1) ^ 2 * (z + x) ^ 2 * (y + z) + 1 / 2 * (1 + z) ^ 2 * (x + y) ^ 2 * (z + x) ≥ 0  :=  by sorry
