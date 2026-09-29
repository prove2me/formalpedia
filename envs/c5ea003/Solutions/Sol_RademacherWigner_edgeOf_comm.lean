-- Prove2me | solution 1 for RademacherWigner.edgeOf_comm
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:04:39.658192+00:00
-- url     : https://prove2.me/submissions/43d7b3eb-37a3-4ed9-9486-4c4fe4de5dc3

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
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
theorem solution(i j : Fin N) : edgeOf i j = edgeOf j i := by
  unfold edgeOf
  rcases lt_trichotomy i j with h | h | h
  · simp [h, not_lt.2 h.le]
  · simp [h]
  · simp [h, not_lt.2 h.le]
