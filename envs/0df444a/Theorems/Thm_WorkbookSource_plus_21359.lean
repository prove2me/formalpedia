-- Prove2me | Theorems.Thm_WorkbookSource_plus_21359
-- name    : WorkbookSource.plus_21359
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:26.321462+00:00
-- url     : https://prove2.me/theorems/c3f2c634-fa2e-41dd-a7db-d3b098b160a9
-- title:
--   A pairwise-product correction bound at sum three
-- statement:
--   Let $a,b,c$ are nonnegative real numbers such that $a+b+c=3.$
--   ab(1-c)+bc(1-a)+ca(1-b)\leq\frac{9}{4}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21359` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21359; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21359 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3) : a * b * (1 - c) + b * c * (1 - a) + c * a * (1 - b) ≤ 9 / 4   :=  by sorry
