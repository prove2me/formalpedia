-- Prove2me | solution 1 for RademacherWigner.trace_pow_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:51:41.343716+00:00
-- url     : https://prove2.me/submissions/8ada0fc5-762d-4dae-b7ed-86fa90fff494

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

/-- Reversing the order of three nested sums. -/
theorem sum_reverse3 (G : Fin N → Fin N → Fin N → ℝ) :
    (∑ b, ∑ c, ∑ d, G b c d) = ∑ d, ∑ c, ∑ b, G b c d := by
  have h1 : (∑ b, ∑ c, ∑ d, G b c d) = ∑ b, ∑ d, ∑ c, G b c d :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have h2 : (∑ b, ∑ d, ∑ c, G b c d) = ∑ d, ∑ b, ∑ c, G b c d := Finset.sum_comm
  have h3 : (∑ d, ∑ b, ∑ c, G b c d) = ∑ d, ∑ c, ∑ b, G b c d :=
    Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [h1, h2, h3]





















open RademacherWigner in
theorem solution(M : Matrix (Fin N) (Fin N) ℝ) :
    (M ^ 4).trace = ∑ i, ∑ j, ∑ k, ∑ l, M i j * M j k * M k l * M l i := by
  simp only [Matrix.trace, Matrix.diag, show (4:ℕ) = 1 + 1 + 1 + 1 from rfl, pow_succ, pow_zero,
    Matrix.one_mul, Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_reverse3 (fun l k j => M i j * M j k * M k l * M l i)]
