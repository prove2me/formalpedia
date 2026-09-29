-- Prove2me | Theorems.Thm_WorkbookSource_problem_5606
-- name    : WorkbookSource.problem_5606
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:11:14.24045+00:00
-- url     : https://prove2.me/theorems/680c5ca4-d7e2-4a98-a577-d6623dcef5c5
-- title:
--   A difference of two cubes
-- statement:
--   Find the value of $a^n - b^n$ given $a = 4$, $b = 2$, and $n = 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_5606` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_5606; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_5606 (a b n : ℕ) (hab : a = 4 ∧ b = 2) (hn : n = 3) : a^n - b^n = 56  :=  by sorry
