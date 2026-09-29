-- Prove2me | Theorems.Thm_lean_workbook_plus_41069
-- name    : lean_workbook_plus_41069
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/eb89dbf3-c277-4698-a741-7eee476704c4
-- statement:
--   We will form a recursive sequence with initial conditions $a_0=0$ and $a_1=1$ where $a_n$ represents the number of ways $A$ can receive the ball after $n$ passes. So for the $n$ th term of the sequence, we have 2 cases. Case 1: If the $n-2$ th place is $A$ . In this case, there are $a_{n-2}$ ways of arriving to this point and clearly the $n-1$ th place can be $B,C,D$ . So the total ways of having the $n$ th position as $A$ is $\boxed{3a_{n-2}}$ . Case 2: If the $n-2$ th position is not $A$ , say $X$ , for some $X \in \{B,C,D\}$ . Then, in this case we cannot have the $n-1$ th place as $A$ (since the $n$ th place will be $A$ ) or $X$ (since the $n-2$ th place is already $X$ ). So we have $\boxed{2a_{n-1}}$ ways in this case. So are recursion can be written as $a_n=2a_{n-1}+3a_{n-2}$ with initial conditions $(a_0,a_1)=(0,1)$ . So solving the characteristic equation and finding the coefficients, we get $\boxed{a_n=\frac{3^n-(-1)^n}{4}}$ . Let $n=7$ to get $a_7=2188/4=547$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41069  (a : ℕ → ℚ)
  (h₀ : a 0 = 0)
  (h₁ : a 1 = 1)
  (h₂ : ∀ n, a (n + 2) = 2 * a (n + 1) + 3 * a n) :
  a 7 = 547   :=  by sorry
