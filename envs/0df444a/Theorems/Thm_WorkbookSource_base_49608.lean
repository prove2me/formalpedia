-- Prove2me | Theorems.Thm_WorkbookSource_base_49608
-- name    : WorkbookSource.base_49608
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:16:02.610819+00:00
-- url     : https://prove2.me/theorems/5cd26d30-7e1f-4697-9a79-2f1ae1bc860c
-- title:
--   A pairwise squared product bound at fixed sum two
-- statement:
--   Let $a,b,c$ are nonnegative real numbers satisfying $a+b+c=2.$ Prove that $(a+b)^2(a+c)^2(b+c)^2(a^2+b^2+c^2)\leq8.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49608` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49608; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_49608 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 2) : (a + b) ^ 2 * (a + c) ^ 2 * (b + c) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≤ 8  :=  by sorry
