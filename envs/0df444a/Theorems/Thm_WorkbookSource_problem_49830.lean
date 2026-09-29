-- Prove2me | Theorems.Thm_WorkbookSource_problem_49830
-- name    : WorkbookSource.problem_49830
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:13:58.331987+00:00
-- url     : https://prove2.me/theorems/b3d9ce0f-b5e6-49ad-984c-f359bf763d34
-- title:
--   The complete zero set of a quadratic function
-- statement:
--   Find the solutions for $f(x)=0$ where $f(x)=x^2-2x$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_49830` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_49830; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_49830 (f : ℝ → ℝ) (x : ℝ) (f_def : f x = x^2 - 2*x) : f x = 0 ↔ x = 0 ∨ x = 2  :=  by sorry
