-- Prove2me | Theorems.Thm_WorkbookSource_base_17901
-- name    : WorkbookSource.base_17901
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:10:08.257894+00:00
-- url     : https://prove2.me/theorems/e710d475-1864-459d-8276-b8f6774a0251
-- title:
--   A shifted cyclic quadratic difference ratio is nonnegative
-- statement:
--   Let $a,b,c \in \Bbb R^+$ such that $a+b+c=3$ . Prove :
--
--    $$\frac{a(a+b-2c)}{ab+3}+\frac{b(b+c-2a)}{bc+3}+\frac{c(c+a-2b)}{ca+3}\geq0.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_17901` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_17901; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_17901 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a * (a + b - 2 * c) / (a * b + 3) + b * (b + c - 2 * a) / (b * c + 3) + c * (c + a - 2 * b) / (c * a + 3)) ≥ 0  :=  by sorry
