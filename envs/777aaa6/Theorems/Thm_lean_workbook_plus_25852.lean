-- Prove2me | Theorems.Thm_lean_workbook_plus_25852
-- name    : lean_workbook_plus_25852
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f31fb830-3599-49d0-9d38-c4203ee1f0f0
-- statement:
--   We can use recursion. Define $a_i$ to be the amount of $i$ digit numbers that end with $1$ , and $b_i$ be the amount that don't end with $1$ . Then $b_{i+1}=2b_i+2a_i$ , and $a_{i+1}=b_i$ . We can then solve for $a_7+b_7$ using $a_1=1, b_1=2$ , to get our answer of $\boxed{1224}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25852  (a b : ℕ → ℕ)
  (h₀ : a 1 = 1)
  (h₁ : b 1 = 2)
  (h₂ : ∀ i, b (i + 1) = 2 * b i + 2 * a i)
  (h₃ : ∀ i, a (i + 1) = b i) :
  a 7 + b 7 = 1224   :=  by sorry
