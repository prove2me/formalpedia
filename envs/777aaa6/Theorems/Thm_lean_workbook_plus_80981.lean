-- Prove2me | Theorems.Thm_lean_workbook_plus_80981
-- name    : lean_workbook_plus_80981
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/90af1bc1-8461-484c-ac05-66fc38c8df53
-- statement:
--   Let $ a_n$ represent the number of strings of length $ n$ such that there are no consecutive $ 1$ s. Clearly $ a_{0} = 1, a_{1} = 2$ . Any string of length $ n+1$ is composed of a string of length $ n$ and one additional number. If the last digit is a $ 2$ , then any of $ a_n$ strings of length $ n$ can precede it. If the last digit is a $ 1$ , then the second to last digit must be a $ 2$ , and any of $ a_{n-1}$ strings of length $ n-1$ can precede it. Thus we have the recursion $ a_{n+1} = a_{n} + a_{n-1}$ which indeed is the Fibonacci sequence, except with indexes shifted. Matching them, we have $ a_n = F_{n+2}$ , and $ a_{11} = F_{13} = \boxed{233}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80981  (a : ℕ → ℕ)
  (h₀ : a 0 = 1)
  (h₁ : a 1 = 2)
  (h₂ : ∀ n, a (n + 2) = a (n + 1) + a n) :
  a 11 = 233   :=  by sorry
