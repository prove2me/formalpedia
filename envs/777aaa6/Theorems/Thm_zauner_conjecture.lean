-- Prove2me | Theorems.Thm_zauner_conjecture
-- name    : zauner_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T20:14:34.126376+00:00
-- url     : https://prove2.me/theorems/dbce67ec-cd0f-4911-9655-08081e4eaf98
-- statement:
--   Zauner's conjecture (1999): For every dimension d, there exists a set of d² unit vectors in ℂᵈ forming a SIC-POVM (symmetric informationally complete positive operator-valued measure), i.e., equiangular lines with |⟨ψᵢ,ψⱼ⟩|² = 1/(d+1) for all i≠j. Verified in many dimensions; proof for all d is open.
-- source:
--   https://en.wikipedia.org/wiki/SIC-POVM

import Mathlib

import Mathlib

theorem zauner_conjecture (d : ℕ) (hd : 1 ≤ d) :
    ∃ (phi : Fin (d^2) → EuclideanSpace ℂ (Fin d)),
      (∀ i, ‖phi i‖ = 1) ∧
      ∀ i j : Fin (d^2), i ≠ j →
        Complex.normSq (inner (𝕜 := ℂ) (phi i) (phi j)) = 1 / (d + 1 : ℝ) := by
  sorry
