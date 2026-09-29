-- Prove2me | Theorems.Thm_WorkbookSource_problem_33759
-- name    : WorkbookSource.problem_33759
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:53.214255+00:00
-- url     : https://prove2.me/theorems/02b5f1e4-db8d-4c16-b638-93111d26bf0d
-- title:
--   Nonnegativity of a shifted cube
-- statement:
--   Let $a$ be real with $a>-1$. Then
--
--   $$ (a+1)^3\ge0. $$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33759` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33759; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_33759 (a : ℝ) (h : a > -1) : (a + 1)^3 ≥ 0  :=  by sorry
