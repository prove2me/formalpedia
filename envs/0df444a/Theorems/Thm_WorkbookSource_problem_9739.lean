-- Prove2me | Theorems.Thm_WorkbookSource_problem_9739
-- name    : WorkbookSource.problem_9739
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:46:24.05846+00:00
-- url     : https://prove2.me/theorems/2440584b-70c7-436c-9381-82aff65d7f26
-- title:
--   Evaluating a reciprocal functional equation
-- statement:
--   If f is a function such that $f(x)+\frac{1}{x}\left[f\left(-\frac{1}{x}\right)\right]=3$, what is the value of $f(2)$? Express your answer as a common fraction.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_9739` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_9739; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_9739 (f : ℝ → ℝ) (hf : ∀ x, f x + 1/x * f (-1/x) = 3) : f 2 = 3/4  :=  by sorry
