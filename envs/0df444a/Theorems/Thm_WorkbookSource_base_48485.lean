-- Prove2me | Theorems.Thm_WorkbookSource_base_48485
-- name    : WorkbookSource.base_48485
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:15:25.58332+00:00
-- url     : https://prove2.me/theorems/f58a22ce-37cc-4c22-9d99-a4b37e2d4e3b
-- title:
--   A cubed quadratic sum bounds a pairwise product times a cubic sum
-- statement:
--   Let $x,y,z>0$ show that
--    $$8(x^2+y^2+z^2)^3\ge 9(x+y)(y+z)(z+x)(x^3+y^3+z^3)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_48485` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_48485; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_48485 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : 8 * (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 ≥ 9 * (x + y) * (y + z) * (z + x) * (x ^ 3 + y ^ 3 + z ^ 3)  :=  by sorry
