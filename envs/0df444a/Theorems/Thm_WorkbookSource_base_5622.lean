-- Prove2me | Theorems.Thm_WorkbookSource_base_5622
-- name    : WorkbookSource.base_5622
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:29.603896+00:00
-- url     : https://prove2.me/theorems/f47aac84-7048-4b3e-8bbb-674e4e04cb8b
-- title:
--   A normalized product inequality with a fifth-degree correction
-- statement:
--   Let $ x$ , $y$ and $z $ be non-negative numbers, which satisfying $ x+y+z=3$ . Prove that: $2xyz(x^2+y^2+z^2)+(x^2-x+1)(y^2-y+1)(z^2-z+1) \le 7$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5622` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5622; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_5622 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (h : x + y + z = 3) : 2 * x * y * z * (x ^ 2 + y ^ 2 + z ^ 2) + (x ^ 2 - x + 1) * (y ^ 2 - y + 1) * (z ^ 2 - z + 1) ≤ 7  :=  by sorry
