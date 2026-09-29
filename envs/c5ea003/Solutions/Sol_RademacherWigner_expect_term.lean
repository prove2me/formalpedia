-- Prove2me | solution 1 for RademacherWigner.expect_term
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:49:44.860318+00:00
-- url     : https://prove2.me/submissions/ef96ffa2-25e4-4ad2-9a85-f790528507ad

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_expect_const
import Theorems.Thm_RademacherWigner_expect_term_eq_zero
import Theorems.Thm_RademacherWigner_expect_zero
import Theorems.Thm_RademacherWigner_term_eq_one
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# The symmetric Rademacher Wigner ensemble and its spectral moments

This file constructs a concrete Wigner ensemble — the uniform measure on real
symmetric `N × N` sign matrices with zero diagonal — and computes the first
nontrivial normalised spectral moments of `W/√N` by the moment method:

* the second moment is **deterministically** `1 - 1/N` (self-averaging), and
* the expected fourth moment is exactly `(N-1)(2N-3)/N²`.

Both converge to the corresponding moments of the Wigner semicircle law,
`C₁ = 1` and `C₂ = 2` (see `Probability.WignerSemicircleMoments`), which is the
moment-method statement of the semicircle law at orders 2 and 4.

The key probabilistic input is a *sign-flip involution*: if some edge of the
closed walk `i → j → k → l → i` is traversed an odd number of times, flipping
the corresponding Rademacher variable negates the summand, so the expectation
vanishes.  This replaces the usual independence/factorisation argument by an
exact combinatorial symmetry.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}










theorem entry_diag (g : Config N) (i : Fin N) : entry g i i = 0 := by simp [entry]





/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/






















open RademacherWigner in
theorem solution(i j k l : Fin N) :
    expect (fun g : Config N => entry g i j * entry g j k * entry g k l * entry g l i) =
      pairedWalk i j k l := by
  by_cases hij : i = j
  · have h0 : ∀ g : Config N,
        entry g i j * entry g j k * entry g k l * entry g l i = 0 := by
      intro g; simp [hij, entry_diag]
    simp only [h0]
    rw [expect_zero, pairedWalk, if_neg (by tauto)]
  by_cases hjk : j = k
  · have h0 : ∀ g : Config N,
        entry g i j * entry g j k * entry g k l * entry g l i = 0 := by
      intro g; simp [hjk, entry_diag]
    simp only [h0]
    rw [expect_zero, pairedWalk, if_neg (by tauto)]
  by_cases hkl : k = l
  · have h0 : ∀ g : Config N,
        entry g i j * entry g j k * entry g k l * entry g l i = 0 := by
      intro g; simp [hkl, entry_diag]
    simp only [h0]
    rw [expect_zero, pairedWalk, if_neg (by tauto)]
  by_cases hli : l = i
  · have h0 : ∀ g : Config N,
        entry g i j * entry g j k * entry g k l * entry g l i = 0 := by
      intro g; simp [hli, entry_diag]
    simp only [h0]
    rw [expect_zero, pairedWalk, if_neg (by tauto)]
  by_cases hpair : i = k ∨ j = l
  · have h1 : ∀ g : Config N,
        entry g i j * entry g j k * entry g k l * entry g l i = 1 := fun g =>
      term_eq_one g hij hjk hkl hli hpair
    simp only [h1]
    rw [expect_const, pairedWalk, if_pos ⟨hij, hjk, hkl, hli, hpair⟩]
  · push_neg at hpair
    rw [pairedWalk, if_neg (by tauto)]
    exact expect_term_eq_zero hij hjk hkl hli hpair.1 hpair.2
