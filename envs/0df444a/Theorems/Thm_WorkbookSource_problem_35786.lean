-- Prove2me | Theorems.Thm_WorkbookSource_problem_35786
-- name    : WorkbookSource.problem_35786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:47.694293+00:00
-- url     : https://prove2.me/theorems/57d4e8ff-4f5f-4356-a410-8ad878e3356a
-- title:
--   Determining a quadratic coefficient from a value
-- statement:
--   Let $c\in\mathbb R$ and $f:\mathbb R\to\mathbb R$ satisfy $f(x)=x^2-5x+3c$ for every real $x$. If $f(3)=-12$, then
--
--   $$c=-2.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_35786` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_35786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_35786  (c : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = x^2 - 5 * x + 3 * c)
  (h₁ : f 3 = -12) :
  c = -2  :=  by sorry
