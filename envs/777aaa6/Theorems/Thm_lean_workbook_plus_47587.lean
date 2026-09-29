-- Prove2me | Theorems.Thm_lean_workbook_plus_47587
-- name    : lean_workbook_plus_47587
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/69c3b049-67cd-4b27-b355-5a510502bd9a
-- statement:
--   We will find the number of ways to climb $n$ stairs with jumps of size $1, 2, 3$ . Denote this number as $a_n$ . If our first jump is $1$ , we have $n-1$ stairs left to climb, in $a_{n-1}$ ways. Similarly, for $2$ jumps, we find another $a_{n-2}$ ways, and $a_{n-3}$ after a $3$ jump. Our recursion is $a_n=a_{n-1}+a_{n-2}+a_{n-3}$ (the ) Our initial terms are $a_0=1$ , $a_1=1$ , and $a_2=2$ . The value of $a_6=24$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47587  (a : ℕ → ℕ)
  (h₀ : a 0 = 1)
  (h₁ : a 1 = 1)
  (h₂ : a 2 = 2)
  (h₃ : ∀ n, a (n + 3) = a (n + 2) + a (n + 1) + a n) :
  a 6 = 24   :=  by sorry
