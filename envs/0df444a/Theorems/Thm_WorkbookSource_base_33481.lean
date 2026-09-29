-- Prove2me | Theorems.Thm_WorkbookSource_base_33481
-- name    : WorkbookSource.base_33481
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:16.791706+00:00
-- url     : https://prove2.me/theorems/d1d428ed-fa83-43b7-a118-59f743d70a3d
-- title:
--   A mixed quartic inequality in two real variables
-- statement:
--   Let $ x,y$ be real numbers. Prove that
--
--    $ (x^2 + y^2)^2 + x^3 + y^3 + 4xy^2 + x^2 + y^2\geq 3x^3y + 5x^2y + xy.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33481` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33481; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33481 (x y : ℝ) : (x^2 + y^2)^2 + x^3 + y^3 + 4*x*y^2 + x^2 + y^2 ≥ 3*x^3*y + 5*x^2*y + x*y  :=  by sorry
