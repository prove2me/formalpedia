-- Prove2me | solution 1 for RademacherWigner.term_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:47:27.073021+00:00
-- url     : https://prove2.me/submissions/dacb5749-e6d5-461c-b367-096d0dd306f5

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_edgeOf_comm
import Theorems.Thm_RademacherWigner_sgn_mul_self
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









theorem entry_symm (g : Config N) (i j : Fin N) : entry g i j = entry g j i := by
  unfold entry
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h, edgeOf_comm i j]


theorem entry_mul_self (g : Config N) {i j : Fin N} (h : i ≠ j) :
    entry g i j * entry g i j = 1 := by
  simp [entry, h]




/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/






















open RademacherWigner in
theorem solution{i j k l : Fin N} (g : Config N) (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l)
    (hli : l ≠ i) (h : i = k ∨ j = l) :
    entry g i j * entry g j k * entry g k l * entry g l i = 1 := by
  rcases h with rfl | rfl
  · -- i = k : the walk is i → j → i → l → i, both edges traversed twice
    have h1 : entry g i j * entry g j i = 1 := by
      rw [entry_symm g j i]; exact entry_mul_self g hij
    have h2 : entry g i l * entry g l i = 1 := by
      rw [entry_symm g l i]; exact entry_mul_self g hkl
    calc entry g i j * entry g j i * entry g i l * entry g l i
        = (entry g i j * entry g j i) * (entry g i l * entry g l i) := by ring
      _ = 1 := by rw [h1, h2]; ring
  · -- j = l : the walk is i → j → k → j → i
    have h1 : entry g i j * entry g j i = 1 := by
      rw [entry_symm g j i]; exact entry_mul_self g hij
    have h2 : entry g j k * entry g k j = 1 := by
      rw [entry_symm g k j]; exact entry_mul_self g hjk
    calc entry g i j * entry g j k * entry g k j * entry g j i
        = (entry g i j * entry g j i) * (entry g j k * entry g k j) := by ring
      _ = 1 := by rw [h1, h2]; ring
