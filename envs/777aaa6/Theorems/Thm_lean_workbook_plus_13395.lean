-- Prove2me | Theorems.Thm_lean_workbook_plus_13395
-- name    : lean_workbook_plus_13395
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f54d3a51-9958-4c40-a81d-5823a5ffb234
-- statement:
--   Let $ a_{1}, a_{2}, .... a_{n} $ be positive and distinct real numbers with $ a_{1} + a_{2} + .... + a_{n} = n $ . Demonstrate that the function $ f : [1, \infty) \to \mathbb{R} $ defined with $ f(x)= a_{1}^x + a_{2}^x + ... +a_{n}^x $ is a strictly increasing function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13395 (n : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 < a i) (hab : a.Injective) (h : ∑ i, a i = n) : StrictMono (fun x : ℝ ↦ ∑ i : Fin n, (a i)^x)   :=  by sorry
