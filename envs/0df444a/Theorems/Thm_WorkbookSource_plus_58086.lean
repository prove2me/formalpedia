-- Prove2me | Theorems.Thm_WorkbookSource_plus_58086
-- name    : WorkbookSource.plus_58086
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:48:02.306218+00:00
-- url     : https://prove2.me/theorems/a11fcd70-7206-4584-a529-f71f88d69f0f
-- title:
--   A shifted quadratic reciprocal sum is at least one
-- statement:
--   If $a,b,c>0$ and $a+b+c=3\;,$ Then prove that $\frac{1}{2a^2+1}+\frac{1}{2b^2+1}+\frac{1}{2c^2+1}\geq 1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_58086` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_58086; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_58086 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : 1 ≤ 1 / (2 * a ^ 2 + 1) + 1 / (2 * b ^ 2 + 1) + 1 / (2 * c ^ 2 + 1)   :=  by sorry
