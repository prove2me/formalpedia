-- Prove2me | Theorems.Thm_WorkbookSource_problem_13737
-- name    : WorkbookSource.problem_13737
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T15:02:45.874897+00:00
-- url     : https://prove2.me/theorems/ede82af7-3efb-4292-895b-88b867b94bcd
-- title:
--   A five-equation cyclic linear system
-- statement:
--   Find the solution for the specific system of 5 equations with RHS's = 3: $x_{1}+x_{2}+x_{3}=3$, $x_{2}+x_{3}+x_{4}=3$, $x_{3}+x_{4}+x_{5}=3$, $x_{4}+x_{5}+x_{1}=3$, $x_{5}+x_{1}+x_{2}=3$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13737` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13737; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_13737 (x1 x2 x3 x4 x5 : ℝ) : x1 + x2 + x3 = 3 ∧ x2 + x3 + x4 = 3 ∧ x3 + x4 + x5 = 3 ∧ x4 + x5 + x1 = 3 ∧ x5 + x1 + x2 = 3 ↔ x1 = 1 ∧ x2 = 1 ∧ x3 = 1 ∧ x4 = 1 ∧ x5 = 1  :=  by sorry
