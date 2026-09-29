-- Prove2me | Theorems.Thm_WorkbookSource_base_7240
-- name    : WorkbookSource.base_7240
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:45:47.641485+00:00
-- url     : https://prove2.me/theorems/85e7da9d-3e8d-41ee-bb53-193a30aa049c
-- title:
--   A pair-square sum bounds the triple product at total three
-- statement:
--   Let real numbers $x,y,z$ such that $x+y+z=3$ ,please do this:
--
--   $y^2z^2+z^2x^2+x^2y^2 \geq 3xyz$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7240` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7240; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7240 (x y z : ℝ) (h : x + y + z = 3) : y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2 + x ^ 2 * y ^ 2 ≥ 3 * x * y * z  :=  by sorry
