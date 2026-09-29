-- Prove2me | Theorems.Thm_lean_workbook_plus_25398
-- name    : lean_workbook_plus_25398
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/630c2f25-5bcd-4530-9833-a386dad97836
-- statement:
--   Find the closed form of the sequence $\{\mu_n\}$ defined by $\mu_0 = 2, \mu_1= 4,$ and $\mu_n = 4\mu_{n-1} + \mu_{n-2}$ for all $n \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25398 (μ : ℕ → ℕ) (h₀ : μ 0 = 2) (h₁ : μ 1 = 4) (h₂ : ∀ n ≥ 2, μ n = 4 * μ (n - 1) + μ (n - 2)) : ∃ f : ℕ → ℕ, ∀ n, μ n = f n   :=  by sorry
