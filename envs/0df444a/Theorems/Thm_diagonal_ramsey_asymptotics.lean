-- Prove2me | Theorems.Thm_diagonal_ramsey_asymptotics
-- name    : diagonal_ramsey_asymptotics
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T01:51:15.555346+00:00
-- url     : https://prove2.me/theorems/930f45d0-14b4-43df-bd5d-68a646daf969
-- statement:
--   Diagonal Ramsey asymptotics: R(k,k) grows like 2^{Θ(k)}. Spencer (1975) gave lower bound Ω(√2^k). Upper bound O(4^k). Recent improvement to (3.993)^k (Campos et al. 2023). Exact exponential base unknown.
-- source:
--   https://en.wikipedia.org/wiki/Ramsey%27s_theorem

import Mathlib

import Mathlib

noncomputable def ramseyDiag (k : ℕ) : ℕ :=
    sInf {n : ℕ | ∀ (col : Sym2 (Fin n) → Bool),
      (∃ S : Finset (Fin n), S.card = k ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = true) ∨
      (∃ S : Finset (Fin n), S.card = k ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = false)}

theorem diagonal_ramsey_asymptotics :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      ((2 : ℝ) ^ (k / 2) ≤ ramseyDiag k) ∧
      (ramseyDiag k ≤ (4 : ℝ) ^ k) := by
  sorry
