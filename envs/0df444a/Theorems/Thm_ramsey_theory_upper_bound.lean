-- Prove2me | Theorems.Thm_ramsey_theory_upper_bound
-- name    : ramsey_theory_upper_bound
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-06-01T03:45:24.933793+00:00
-- url     : https://prove2.me/theorems/eecde50e-1d0e-4ec7-a9cc-e1648e586b86
-- statement:
--   Ramsey theorem upper bound: R(k,k) ≤ 4^k. Proved. The exact value of R(k,k) is open for k ≥ 5. Recent breakthrough: R(k,k) ≤ (4-ε)^k (Campos et al. 2023).
-- source:
--   https://en.wikipedia.org/wiki/Ramsey%27s_theorem

import Mathlib

import Mathlib

theorem ramsey_theory_upper_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ N : ℕ, N ≤ 4 ^ k ∧
    ∀ (n : ℕ) (_ : N ≤ n) (col : Sym2 (Fin n) → Bool),
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = true) ∨
      (∃ S : Finset (Fin n), S.card = k ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = false) := by
  sorry
