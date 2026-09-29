-- Prove2me | Theorems.Thm_WorkbookSource_problem_5176
-- name    : WorkbookSource.problem_5176
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:48.907592+00:00
-- url     : https://prove2.me/theorems/3e2d9934-4147-4bfd-8dec-fa144e178e7b
-- title:
--   A lower bound for a weighted unit sum
-- statement:
--   Let $a,b,c>0$ , $a,b,c\in (0,\frac{1}{2}],a+b+c=1,$ ,prove that:
--
--    $2a+3b+4c\geq \frac{5}{2}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5176` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5176; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_5176 (a b c : ℝ) (ha : 0 < a ∧ a ≤ 1 / 2) (hb : 0 < b ∧ b ≤ 1 / 2) (hc : 0 < c ∧ c ≤ 1 / 2) (hab : a + b + c = 1) : 2 * a + 3 * b + 4 * c ≥ 5 / 2  :=  by sorry
