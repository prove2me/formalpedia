-- Prove2me | solution 1 for RademacherWigner.expect_term_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:33:09.670302+00:00
-- url     : https://prove2.me/submissions/9f6cd482-d4ab-4e71-b4c3-9b75a90a7876

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_edges_ne_first
import Theorems.Thm_RademacherWigner_entry_flipEdge
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















/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/






















open RademacherWigner in
theorem solution{i j k l : Fin N} (hij : i ≠ j) (hjk : j ≠ k) (hkl : k ≠ l)
    (hli : l ≠ i) (hik : i ≠ k) (hjl : j ≠ l) :
    expect (fun g : Config N => entry g i j * entry g j k * entry g k l * entry g l i) = 0 := by
  set p : Fin N × Fin N := edgeOf i j with hp
  obtain ⟨e2, e3, e4⟩ := edges_ne_first hij hjk hkl hli hik hjl
  have hflip : ∀ g : Config N,
      entry (flipEdge p g) i j * entry (flipEdge p g) j k * entry (flipEdge p g) k l *
        entry (flipEdge p g) l i =
      -(entry g i j * entry g j k * entry g k l * entry g l i) := by
    intro g
    rw [entry_flipEdge, entry_flipEdge, entry_flipEdge, entry_flipEdge,
      if_pos rfl, if_neg e2, if_neg e3, if_neg e4]
    ring
  have hsum : (∑ g : Config N, entry g i j * entry g j k * entry g k l * entry g l i) = 0 := by
    have h1 := Equiv.sum_comp (flipEdge (N := N) p)
      (fun g => entry g i j * entry g j k * entry g k l * entry g l i)
    rw [Finset.sum_congr rfl fun g _ => hflip g] at h1
    rw [Finset.sum_neg_distrib] at h1
    linarith
  unfold RademacherWigner.expect
  rw [hsum, zero_div]
