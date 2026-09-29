-- Prove2me | Theorems.Thm_lean_workbook_plus_48572
-- name    : lean_workbook_plus_48572
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9aaca217-aae5-4a93-9d42-ee103970aa91
-- statement:
--   (x+1)^n=\sum_{k=0}^{n}\binom nk x^{k} \n\nn(x+1)^{n-1}=\frac 1x\sum_{k=1}^{n}\binom nk kx^{k} \n\nn(n-1)(x+1)^{n-2}=\frac 1{x^2}\sum_{k=1}^{n}\binom nk k^2x^k \n\nLet $ x=1$ . \n\nboxed{n(n-1)2^{n-2}}=\sum_{k=1}^{n}\binom nk k^2
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48572 : ∀ n : ℕ, n * (n - 1) * 2 ^ (n - 2) = ∑ k in Finset.Icc 1 n, (Nat.choose n k) * k ^ 2   :=  by sorry
