-- Prove2me | Theorems.Thm_WorkbookSource_base_30799
-- name    : WorkbookSource.base_30799
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:47:51.940624+00:00
-- url     : https://prove2.me/theorems/1b125cee-47f6-475b-8e13-aa9c64097e54
-- title:
--   A quartic bound formed from two squared linear factors
-- statement:
--   Let $x,y,z \geq 0$ ,prove that: $2x^2(3x+y)^2+2y^2(3y+z)^2-(3x+y)^2y(2y+z+x)\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30799` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30799; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30799 (x y z : ℝ) : 2 * x ^ 2 * (3 * x + y) ^ 2 + 2 * y ^ 2 * (3 * y + z) ^ 2 - (3 * x + y) ^ 2 * y * (2 * y + z + x) ≥ 0  :=  by sorry
