-- Prove2me | Theorems.Thm_lean_workbook_plus_48480
-- name    : lean_workbook_plus_48480
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7c0b8d95-6d10-461f-857c-839c16fa6978
-- statement:
--   Check $A(n)=B(n)$ for all $n$ where : \n $A(n)=P(n+1)-P(n)$ $=\sum_{k=2}^{2n}\frac{2(-1)^k}k-\frac 2{2n+1}+\frac 1{2n+2}$ \n $B(n)=Q(n+1)-Q(n)$ $=\sum_{k=n+1}^{2n}\frac{-2}k+\frac{2n-1}{2n+1}+\frac{2n+1}{2n+2}+\frac 1{n+1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48480 : ∀ n : ℕ, (∑ k in Finset.Icc 2 (2 * n), (2 * (-1 : ℤ)^k / k) - 2 / (2 * n + 1) + 1 / (2 * n + 2)) = (∑ k in Finset.Icc (n + 1) (2 * n), (-2 : ℤ) / k + (2 * n - 1) / (2 * n + 1) + (2 * n + 1) / (2 * n + 2) + 1 / (n + 1))   :=  by sorry
