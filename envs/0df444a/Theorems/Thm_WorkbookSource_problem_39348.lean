-- Prove2me | Theorems.Thm_WorkbookSource_problem_39348
-- name    : WorkbookSource.problem_39348
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:39:54.694363+00:00
-- url     : https://prove2.me/theorems/17105aee-46c9-47ba-bd66-81d83a0172d9
-- title:
--   Isolating a summand in a zero sum
-- statement:
--   For real numbers $a,b,c$ with $a+b+c=0$,
--
--   $$b=-a-c.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39348` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39348; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_39348 (a b c : ℝ) (h : a + b + c = 0) : b = -a - c  :=  by sorry
