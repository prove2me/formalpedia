-- Prove2me | Theorems.Thm_lean_workbook_plus_26056
-- name    : lean_workbook_plus_26056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/c83e767c-cb14-45d9-ba51-c8eb62cd44b2
-- statement:
--   A function $ f$ defined on the positive integers (and taking positive integers values) is given by: \n\n $ \begin{matrix} f(1) = 1, f(3) = 3 \nf(2 \cdot n) = f(n) \nf(4 \cdot n + 1) = 2 \cdot f(2 \cdot n + 1) - f(n) \nf(4 \cdot n + 3) = 3 \cdot f(2 \cdot n + 1) - 2 \cdot f(n), \end{matrix}$ \n\n for all positive integers $ n.$ Determine with proof the number of positive integers $ \leq 1988$ for which $ f(n) = n.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26056  (f : ℕ → ℕ)
  (h₀ : f 1 = 1)
  (h₁ : f 3 = 3)
  (h₂ : ∀ n, f (2 * n) = f n)
  (h₃ : ∀ n, f (4 * n + 1) = 2 * f (2 * n + 1) - f n)
  (h₄ : ∀ n, f (4 * n + 3) = 3 * f (2 * n + 1) - 2 * f n)
  : ∃ A : Finset ℕ, A.card = 1988 ∧ ∀ n ∈ A, f n = n   :=  by sorry
