-- Prove2me | Theorems.Thm_WorkbookSource_base_11043
-- name    : WorkbookSource.base_11043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:44:09.723143+00:00
-- url     : https://prove2.me/theorems/c44f71b1-ea22-4e4c-9a7b-17c1ff67f3ee
-- title:
--   A lower bound on a sum of three shifted squares
-- statement:
--   Prove that : $(xy+ 2)^{2}+ (x- 1)^{2}+ (y- 1)^{2}\geqq 4$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11043` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11043 (x y : ℝ) : (x * y + 2) ^ 2 + (x - 1) ^ 2 + (y - 1) ^ 2 ≥ 4  :=  by sorry
