-- Prove2me | Theorems.Thm_WorkbookSource_problem_2789
-- name    : WorkbookSource.problem_2789
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:34.494792+00:00
-- url     : https://prove2.me/theorems/24be5994-9e30-4852-9ada-6359f2b8ce55
-- title:
--   A weighted linear and quadratic constraint bounds the sum
-- statement:
--   Let $a,b,c$ be real numbers such that $a+2b+c=a^2+2b^2+c^2. $ Prove that
--
--    $$a+2b+c \leq 4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2789` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2789; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_2789 (a b c : ℝ) (h : a + 2 * b + c = a^2 + 2 * b^2 + c^2) : a + 2 * b + c ≤ 4  :=  by sorry
