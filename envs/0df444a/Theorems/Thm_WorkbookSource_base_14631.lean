-- Prove2me | Theorems.Thm_WorkbookSource_base_14631
-- name    : WorkbookSource.base_14631
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:37:30.022579+00:00
-- url     : https://prove2.me/theorems/96037256-0aff-4722-af83-89b973fc68f8
-- title:
--   A cubic bound under a weighted nonnegative sum constraint
-- statement:
--   Let $a,b,c\ge 0 $ and $a+2b+c=6$ Prove that
--    $$ a+ab+abc\leq 9$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_14631` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_14631; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_14631 (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a + 2 * b + c = 6) : a + a * b + a * b * c ≤ 9  :=  by sorry
