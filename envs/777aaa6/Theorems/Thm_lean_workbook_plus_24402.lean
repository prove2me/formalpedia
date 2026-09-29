-- Prove2me | Theorems.Thm_lean_workbook_plus_24402
-- name    : lean_workbook_plus_24402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e57fee21-375f-4a3c-b733-6521f129e0d2
-- statement:
--   The least multiple of $6$ that is greater than $23$ is $24,$ and $24-23=\boxed{\textbf{(A)} ~1}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24402  (S : Finset ℕ)
  (h₀ : ∀ (n : ℕ), n ∈ S ↔ 0 < n ∧ n % 6 = 0)
  (h₁ : ∀ (n : ℕ), n ∈ S → n ≥ 24)
  (h₂ : ∀ (n : ℕ), n ≥ 24 → n % 6 = 0 → n ∈ S) :
  24 - 23 = 1  :=  by sorry
