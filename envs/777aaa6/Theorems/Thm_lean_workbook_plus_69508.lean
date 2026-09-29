-- Prove2me | Theorems.Thm_lean_workbook_plus_69508
-- name    : lean_workbook_plus_69508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/09148fc3-1f83-442c-8290-49d99255a9f5
-- statement:
--   For $k \in \{1,2,...,n\}$ we have $(x_{k}-x_{1})\ge 0$ and $(x_{k}-x_{n})\le 0$ .Therefore $(*)\; \; \; (x_{k}-x_{1})(x_{k}-x_{n})\le 0 \; \; ,\; \forall k \in \{1,2,...,n\}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69508  (n : ℕ)
  (x : ℕ → ℝ)
  (h₀ : 0 < n)
  (h₁ : ∀ k, 1 ≤ k ∧ k ≤ n → (x k - x 1) ≥ 0)
  (h₂ : ∀ k, 1 ≤ k ∧ k ≤ n → (x k - x n) ≤ 0) :
  ∀ k, 1 ≤ k ∧ k ≤ n → (x k - x 1) * (x k - x n) ≤ 0   :=  by sorry
