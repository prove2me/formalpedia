-- Prove2me | Theorems.Thm_WorkbookSource_problem_6261
-- name    : WorkbookSource.problem_6261
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:39:50.080498+00:00
-- url     : https://prove2.me/theorems/3ef81e85-c694-43bf-b21b-d9422d0266e6
-- title:
--   Two functional relations force the zero function
-- statement:
--   $P(x,-1)\implies f(x-1)=f(-x).P(x-1,1)\implies f(x)=3f(x-1)$ . Substituting $f(x-1)$ from first into the second yields $$f(x)=3f(-x).$$ Let $x=x$ and $x=-x$ into the past function to get $f(x)=3f(-x)$ and $f(-x)=3f(x).$ Substituting the $f(-x)$ from the second into the first yields $f(x)=3f(-x)=3(3f(x))=9f(x)\implies \boxed{f(x)=0}.$ We can easily check that this function works.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6261` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6261; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_6261  (f : ℝ → ℝ)
  (h₀ : ∀ x, f (x - 1) = f (-x))
  (h₁ : ∀ x, f x = 3 * f (x - 1)) :
  f = λ _ => 0  :=  by sorry
