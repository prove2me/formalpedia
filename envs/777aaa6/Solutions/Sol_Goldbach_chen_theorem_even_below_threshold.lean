-- Prove2me | solution 1 for Goldbach.chen_theorem_even_below_threshold
-- status  : ACCEPTED   (disprove)
-- author  : @moona3k
-- created : 2026-10-04T16:42:30.780496+00:00
-- url     : https://prove2.me/submissions/6c01e8d7-6965-4dc4-a4c7-50b6e292ce8d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option autoImplicit false

-- The same defective statement is already Disproved in the newer platform environment.
-- This checks its still-Open copy at Mathlib 777aaa6; no novelty is claimed.
-- Prior accepted counterexample: Nickrobbins95, submission
-- a735e183-6458-4164-8319-4a59d18afde1 (Mathlib 0df444a).
theorem solution : ¬ (∀ N₀ : ℕ, ∀ n : ℕ, Even n → n < N₀ →
      ∃ p q : ℕ, Nat.Prime p ∧
        (Nat.Prime q ∨ ∃ r s : ℕ, Nat.Prime r ∧ Nat.Prime s ∧ q = r * s) ∧ n = p + q) := by
  intro h
  obtain ⟨p,q,hp,hq,heq⟩ := h 1 0 (by norm_num) (by norm_num)
  have hp2 := hp.two_le
  omega

#print axioms solution
