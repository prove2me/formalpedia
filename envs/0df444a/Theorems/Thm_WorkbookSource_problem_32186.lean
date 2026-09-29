-- Prove2me | Theorems.Thm_WorkbookSource_problem_32186
-- name    : WorkbookSource.problem_32186
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T12:41:00.754037+00:00
-- url     : https://prove2.me/theorems/4e0e662d-65a9-4292-bb9d-683875516499
-- title:
--   A value fixed by a functional equation
-- statement:
--   Given $ f(0)=0, f(1)=1$, and $ f(x^2+\frac{1}{x})=f(x)^2+f(\frac{1}{x})$ for all $ x
--   eq 0$, find $ f(2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32186` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32186; Apache-2.0

import Mathlib
open Real

theorem WorkbookSource.problem_32186 (f : ℝ → ℝ) (hf1 : f 0 = 0) (hf2 : f 1 = 1) (hf3 : ∀ x ≠ 0, f (x^2 + 1/x) = (f x)^2 + f (1/x)) : f 2 = 2  :=  by sorry
