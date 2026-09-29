-- Prove2me | Theorems.Thm_ramsey_r5_5_exact
-- name    : ramsey_r5_5_exact
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:56:18.336336+00:00
-- url     : https://prove2.me/theorems/248ae5f3-3664-4012-9eda-111587b4934e
-- statement:
--   Ramsey number R(5,5): The minimum n such that every 2-coloring of K_n contains a monochromatic K_5. Known: 43 ≤ R(5,5) ≤ 48. Exact value unknown despite being one of the most famous open problems in combinatorics. Erdős joked that alien computing power would be needed to compute it.
-- source:
--   https://en.wikipedia.org/wiki/Ramsey%27s_theorem

import Mathlib

import Mathlib

theorem ramsey_r5_5_exact :
    ∀ (n : ℕ), 43 ≤ n →
    ∀ (col : Sym2 (Fin n) → Bool),
      (∃ S : Finset (Fin n), S.card = 5 ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = true) ∨
      (∃ S : Finset (Fin n), S.card = 5 ∧
        ∀ a ∈ S, ∀ b ∈ S, a ≠ b → col (Sym2.mk a b) = false) := by
  sorry
