-- Prove2me | Theorems.Thm_lean_workbook_plus_57587
-- name    : lean_workbook_plus_57587
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/e7658b9a-8d05-42f3-b7ba-4769e56134eb
-- statement:
--   Prove that : \n $ (C^0_n)^2 + (C^1_n)^2+...+ (C^n_n)^2=(C^n_{2n})^2 $ \n\nJust consider $2n$ different balls and split them in two bags containing each $n$ balls. \n\nIn order to pick up $n$ balls thru these $2n$ , you have $\binom{2n}n$ possibilities which may be split in : \n\nCases where the $n$ balls are composed with $0$ balls of bag $1$ and $n$ balls of bag 2 : \n $\binom n0\times\binom nn=\binom n0^2$ \n\n+ cases where the $n$ balls are composed with $1$ ball of bag $1$ and $n-1$ balls of bag $2$ : \n $\binom n1\times\binom n{n-1}=\binom n1^2$ \n\n+ cases where the $n$ balls are composed with $2$ balls of bag $1$ and $n-2$ balls of bag $2$ : \n $\binom n2\times\binom n{n-2}=\binom n2^2$ \n\n+ ... \n\n+ cases where the $n$ balls are composed with $n$ balls of bag $1$ and $0$ balls of bag $2$ : \n $\binom nn\times\binom n{0}=\binom nn^2$ \n\nAnd so $\boxed{\sum_{k=0}^n\binom nk^2=\binom{2n}n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57587 : ∀ n, ∑ k in Finset.range (n+1), (Nat.choose n k)^2 = (Nat.choose (2 * n) n)^2   :=  by sorry
