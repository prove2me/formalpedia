-- Prove2me | Theorems.Thm_WorkbookSource_problem_27585
-- name    : WorkbookSource.problem_27585
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:56:32.762214+00:00
-- url     : https://prove2.me/theorems/ea08b9a8-7aaf-4033-a9e0-4f7f3a8c2fab
-- title:
--   The value at zero of an exponential functional equation
-- statement:
--   Find the value of $f(0)$ given $f(x+y)=3^{y}f(x)+2^{x}f(y)$ for all real numbers $x$ and $y$ and $f(1)=1$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_27585` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_27585; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_27585 (f : ℝ → ℝ) (hf : ∀ x y : ℝ, f (x + y) = 3 ^ y * f x + 2 ^ x * f y) (h₁ : f 1 = 1) : f 0 = 0  :=  by sorry
