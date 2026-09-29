-- Prove2me | solution 1 for RademacherWigner.edges_ne_first
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:16:10.563409+00:00
-- url     : https://prove2.me/submissions/013aab53-809e-4e80-a93d-aaa4766a7880

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_edgeOf_eq_iff
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
    edgeOf j k ≠ edgeOf i j ∧ edgeOf k l ≠ edgeOf i j ∧ edgeOf l i ≠ edgeOf i j := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rcases (edgeOf_eq_iff hjk hij).1 h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hij h1.symm
    · exact hik h2.symm
  · intro h
    rcases (edgeOf_eq_iff hkl hij).1 h with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hik h1.symm
    · exact hli h2
  · intro h
    rcases (edgeOf_eq_iff hli hij).1 h with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact hli h1
    · exact hjl h1.symm
