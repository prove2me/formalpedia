-- Prove2me | Theorems.Thm_lean_workbook_plus_55224
-- name    : lean_workbook_plus_55224
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/c03c4d6e-3494-4243-ae9a-6c02f36c1834
-- statement:
--   Using development of $e^x$ , you have $\sum_{n=0}^{+\infty}\frac 1{n!}=e$ , $\sum_{n=0}^{+\infty}\frac 1{(2n)!}=\frac{e+e^{-1}}2$ and $\sum_{n=0}^{+\infty}\frac 1{(2n+1)!}=\frac{e-e^{-1}}2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55224 : (∑' n : ℕ, (1/(n!))) = Real.exp 1 ∧ (∑' n : ℕ, (1/(2 * n)!)) = (Real.exp 1 + Real.exp (-1)) / 2 ∧ (∑' n : ℕ, (1/(2 * n + 1)!)) = (Real.exp 1 - Real.exp (-1)) / 2   :=  by sorry
