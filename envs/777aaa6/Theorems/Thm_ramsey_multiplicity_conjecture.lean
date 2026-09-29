-- Prove2me | Theorems.Thm_ramsey_multiplicity_conjecture
-- name    : ramsey_multiplicity_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:53:45.299935+00:00
-- url     : https://prove2.me/theorems/38f54a1f-e027-45e1-b895-502f0370ed2a
-- statement:
--   Ramsey multiplicity conjecture: Any 2-coloring of the edges of K_n contains at least (1/2^{C(k,2)})·C(n,k) monochromatic k-cliques on average. For k=3 Goodman's formula gives the exact count. For k≥4, Thomason showed the random coloring is not extremal and the true minimum is larger than this bound.
-- source:
--   https://en.wikipedia.org/wiki/Ramsey_multiplicity

import Mathlib

import Mathlib

theorem ramsey_multiplicity_conjecture (k : ℕ) (hk : 3 ≤ k) :
    ∀ (n : ℕ) (col : Sym2 (Fin n) → Bool),
      (1 : ℝ) / 2 ^ (Nat.choose k 2) * Nat.choose n k ≤
        {S : Finset (Fin n) | S.card = k ∧
          (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
            col (Sym2.mk a b) = true) ∨
          (∀ a ∈ S, ∀ b ∈ S, a ≠ b →
            col (Sym2.mk a b) = false)}.ncard := by
  sorry
