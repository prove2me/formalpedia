-- Prove2me | Theorems.Thm_WorkbookSource_problem_45573
-- name    : WorkbookSource.problem_45573
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:21.175009+00:00
-- url     : https://prove2.me/theorems/6a55ecf7-4d68-4da1-a0e9-819ca90d2d8a
-- title:
--   An iterated recurrence fixes its input
-- statement:
--   We prove by induction that $f(x,n)=x$ . It is true for our base case $n=0$ . Now suppose it is true up to $n=m$ . Notice that
--
--    $$f(x,m+1)=f(f(x,m),m)=f(x,m)=x$$ so it is true for all natural $n$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_45573` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_45573; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_45573 (f : ℕ → ℕ → ℕ) (x : ℕ) (n : ℕ)
  (h₀ : ∀ x, f x 0 = x)
  (h₁ : ∀ x n, f x (n + 1) = f (f x n) n) :
  f x n = x  :=  by sorry
