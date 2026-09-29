-- Prove2me | Theorems.Thm_WorkbookSource_problem_41120
-- name    : WorkbookSource.problem_41120
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:40:30.061193+00:00
-- url     : https://prove2.me/theorems/17e8bf3f-0c59-4929-824c-11f5a7dd087a
-- title:
--   A sum of three specified squares
-- statement:
--   For real numbers $a=14$, $b=1$, and $c=15$,
--
--   $$a^2+b^2+c^2=422.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41120` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41120; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_41120 (a b c : ℝ) (h₁ : a = 14) (h₂ : b = 1) (h₃ : c = 15) : a^2 + b^2 + c^2 = 422  :=  by sorry
