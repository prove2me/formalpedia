-- Prove2me | solution 1 for RademacherWigner.sum_indicator_ne_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T01:11:51.997671+00:00
-- url     : https://prove2.me/submissions/6da914fa-3375-405c-9bbb-b4deb01cbcbe

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_sum_indicator_ne
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
theorem solution(i : Fin N) :
    (∑ j : Fin N, (if i = j then (0:ℝ) else 1)) = (N:ℝ) - 1 := by
  have h : (∑ j : Fin N, (if i = j then (0:ℝ) else 1))
      = ∑ j : Fin N, (if j = i then (0:ℝ) else 1) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · simp [hj]
    · simp [hj, Ne.symm hj]
  rw [h, sum_indicator_ne]
