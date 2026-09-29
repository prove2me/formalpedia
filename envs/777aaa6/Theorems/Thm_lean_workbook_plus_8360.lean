-- Prove2me | Theorems.Thm_lean_workbook_plus_8360
-- name    : lean_workbook_plus_8360
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d8b2ca94-300d-4599-a8d3-1563c9993c37
-- statement:
--   Note that, for $a_n$ , we can construct it by adding on three different types of steps to $a_{n-1}$ , $a_{n-2}$ , and $a_{n-3}$ . Thus, we have the recursion $a_n=a_{n-1}+a_{n-2}+a_{n-3}$ . We can easily find that $a_1=1, a_2=2$ , and $a_3=4$ . Adding several times, we have $a_6=24$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8360  (a : ℕ → ℕ)
  (h₀ : a 1 = 1)
  (h₁ : a 2 = 2)
  (h₂ : a 3 = 4)
  (h₃ : ∀ n, a (n + 3) = a (n + 2) + a (n + 1) + a n) :
  a 6 = 24   :=  by sorry
