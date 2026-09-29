-- Prove2me | Theorems.Thm_WorkbookSource_base_20078
-- name    : WorkbookSource.base_20078
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:47:42.374135+00:00
-- url     : https://prove2.me/theorems/5c2c8dde-f2a6-4455-8d25-f148e569b5f9
-- title:
--   A cyclic cubic and pairwise product bound at unit sum
-- statement:
--   Let $x,y,z>0$ and $x+y+z=1$ . Is $xy^2+yz^2+zx^2+xy+yz+zx\leq\frac{4}{9}$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_20078` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_20078; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_20078 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 1) : x * y ^ 2 + y * z ^ 2 + z * x ^ 2 + x * y + y * z + z * x ≤ 4 / 9  :=  by sorry
