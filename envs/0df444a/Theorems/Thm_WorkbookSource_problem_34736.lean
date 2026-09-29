-- Prove2me | Theorems.Thm_WorkbookSource_problem_34736
-- name    : WorkbookSource.problem_34736
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:04.117591+00:00
-- url     : https://prove2.me/theorems/35af1ca2-92f2-402f-a521-c43d2596a511
-- title:
--   Solving two coupled function values
-- statement:
--   Let $f$ be a function satisfying $f(x)+2f(27-x)=x.$ Find $f(11)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34736` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34736; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_34736 (f : ℝ → ℝ) (hf : ∀ x, f x + 2 * f (27 - x) = x) : f 11 = 7  :=  by sorry
