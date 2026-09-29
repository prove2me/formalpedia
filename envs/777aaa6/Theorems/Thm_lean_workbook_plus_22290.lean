-- Prove2me | Theorems.Thm_lean_workbook_plus_22290
-- name    : lean_workbook_plus_22290
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/44314bab-9b57-4840-bd6a-2a00903dda5a
-- statement:
--   Calculate the sums: $ A=1\\cdot 2+2\\cdot 3+3\\cdot 4+\\cdots+98\\cdot 99$ and $ B=1\\cdot 99+2\\cdot98+3\\cdot97+\\cdots+98\\cdot 2$. Use $ \\sum_{k=1}^n k(k+1)=\\frac{1}{3}n(n+1)(n+2)$, then compute $ A+B.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22290 (A B : ℕ) (h₁ : A = ∑ k in Finset.Icc 1 98, k * (k + 1)) (h₂ : B = ∑ k in Finset.Icc 1 98, k * (99 - k)) : A + B = 489951   :=  by sorry
