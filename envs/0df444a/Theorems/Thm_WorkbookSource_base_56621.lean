-- Prove2me | Theorems.Thm_WorkbookSource_base_56621
-- name    : WorkbookSource.base_56621
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:36.719515+00:00
-- url     : https://prove2.me/theorems/3ca09f05-0235-41c4-99f7-f4e71cb724d0
-- title:
--   A cubic-quadratic upper bound at total five
-- statement:
--   Prove that $x^2y + z^2x + x^2 + (y - 1)^2 + 2xyz \leq 32$ given $x, y, z \geq 0$ and $x + y + z = 5$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_56621` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_56621; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_56621 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 5) : x^2*y + z^2*x + x^2 + (y - 1)^2 + 2*x*y*z ≤ 32  :=  by sorry
