-- Prove2me | Theorems.Thm_WorkbookSource_plus_44787
-- name    : WorkbookSource.plus_44787
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:34.357285+00:00
-- url     : https://prove2.me/theorems/0d867bff-0c6a-4924-b4f5-de1750a6d833
-- title:
--   Two sharp bounds under a circle constraint
-- statement:
--   Let $a ,b$ be real numbers such that $a^2+b^2=8$. Prove that $-12\leq 2(a+b)-ab\leq 6$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44787` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44787; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.plus_44787 (a b : ℝ) (h : a ^ 2 + b ^ 2 = 8) : -12 ≤ 2 * (a + b) - a * b ∧ 2 * (a + b) - a * b ≤ 6   :=  by sorry
