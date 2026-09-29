-- Prove2me | Theorems.Thm_WorkbookSource_base_52236
-- name    : WorkbookSource.base_52236
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:16.174332+00:00
-- url     : https://prove2.me/theorems/2c2cf9a9-274e-4f1d-8452-7ba99900e4f8
-- title:
--   A cubic and linear lower bound on a sphere
-- statement:
--   Let $ x,y,z >0$ and $x^2+y^2+z^2=3$
--   Prove that
--    $$ x^3+y^3+z^3+3(x+y+z) \geq 9+3xyz $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52236` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52236; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52236 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x^2 + y^2 + z^2 = 3) :  x^3 + y^3 + z^3 + 3 * (x + y + z) ≥ 9 + 3 * x * y * z  :=  by sorry
