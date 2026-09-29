-- Prove2me | solution 1 for RademacherWigner.W_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:33:05.106332+00:00
-- url     : https://prove2.me/submissions/6d8c70b5-a776-44f1-8161-26cd2cf2c53c

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_edgeOf_comm
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






/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/






















open RademacherWigner in
theorem solution(g : Config N) : (W g).IsHermitian := by
  ext i j
  simp [W, Matrix.conjTranspose_apply, entry_symm g j i]
