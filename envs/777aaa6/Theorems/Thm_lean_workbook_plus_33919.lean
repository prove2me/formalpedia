-- Prove2me | Theorems.Thm_lean_workbook_plus_33919
-- name    : lean_workbook_plus_33919
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/194596e9-a573-4929-bd69-1003217e2aa4
-- statement:
--   Consider the number $ A = 10x + a$ with $ 10^{n - 1} > x\geq 10^{n - 2}$ ( $ A$ has $ n$ digits) and $ a\in\{0,1,2,3,4,5,6,7,8,9\}$ We want to have $ a10^{n - 1} + x = 9(10x + a)$ and so $ 89x = a(10^{n - 1} - 9)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33919 (n x a : ℕ) (h₁ : 10^(n-1) > x ∧ x ≥ 10^(n-2)) (h₂ : a ∈ Finset.range 10) (h₃ : a*10^(n-1) + x = 9*(10*x + a)) : 89*x = a*(10^(n-1) - 9)   :=  by sorry
