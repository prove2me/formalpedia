-- Prove2me | solution 1 for Goldbach.chen_theorem
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T07:20:44.484948+00:00
-- url     : https://prove2.me/submissions/00dde126-9d9c-4806-b20e-141e8854e03c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Goldbach_chen_theorem_sieve
import Theorems.Thm_Goldbach_chen_theorem_even_below_threshold
import Mathlib

open Goldbach

theorem solution :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Even n →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧
        n = p + q := by
  obtain ⟨N₀, hsieve⟩ := chen_theorem_sieve
  refine ⟨N₀, ?_⟩
  intro n hn heven
  rcases lt_or_ge n N₀ with hlt | hge
  · exact chen_theorem_even_below_threshold N₀ n heven hlt
  · exact hsieve n hge heven
