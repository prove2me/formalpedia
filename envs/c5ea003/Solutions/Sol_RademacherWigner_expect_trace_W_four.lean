-- Prove2me | solution 1 for RademacherWigner.expect_trace_W_four
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:54:37.072972+00:00
-- url     : https://prove2.me/submissions/bff97664-79a1-453d-a4da-3cdabb43019b

-- Sol generated from Probability/WignerRademacherEnsemble.lean
import Mathlib
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSemicircleMoments
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_RademacherWigner_expect_sum
import Theorems.Thm_RademacherWigner_expect_term
import Theorems.Thm_RademacherWigner_sum_indA
import Theorems.Thm_RademacherWigner_sum_indB
import Theorems.Thm_RademacherWigner_sum_indC
import Theorems.Thm_RademacherWigner_trace_pow_four
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



theorem trace_W_four (g : Config N) :
    ((W g) ^ 4).trace =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        entry g i j * entry g j k * entry g k l * entry g l i :=
  trace_pow_four (W g)









/-- Inclusion–exclusion for paired closed 4-walks. -/
theorem pairedWalk_decomp (i j k l : Fin N) :
    pairedWalk i j k l = indA i j k l + indB i j k l - indC i j k l := by
  unfold pairedWalk indA indB indC
  by_cases h1 : k = i <;> by_cases h2 : l = j <;> by_cases h3 : i = j <;> by_cases h4 : l = i <;>
    by_cases h5 : k = j <;> simp_all [eq_comm]







theorem sum_pairedWalk (N : ℕ) :
    (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, pairedWalk i j k l) =
      2 * (N : ℝ) * ((N : ℝ) - 1) ^ 2 - (N : ℝ) * ((N : ℝ) - 1) := by
  have hsplit : (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, pairedWalk i j k l)
      = (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indA i j k l)
        + (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indB i j k l)
        - (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, indC i j k l) := by
    simp_rw [pairedWalk_decomp, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hsplit, sum_indA, sum_indB, sum_indC]
  ring



open RademacherWigner in
theorem solution(N : ℕ) :
    expect (fun g : Config N => ((W g) ^ 4).trace) =
      2 * (N : ℝ) * ((N : ℝ) - 1) ^ 2 - (N : ℝ) * ((N : ℝ) - 1) := by
  have h1 : ∀ g : Config N, ((W g) ^ 4).trace =
      ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        entry g i j * entry g j k * entry g k l * entry g l i := trace_W_four
  simp only [h1]
  rw [expect_sum]
  have h2 : ∀ i : Fin N,
      expect (fun g : Config N => ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N,
        entry g i j * entry g j k * entry g k l * entry g l i)
      = ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, pairedWalk i j k l := by
    intro i
    rw [expect_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [expect_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [expect_sum]
    exact Finset.sum_congr rfl fun l _ => expect_term i j k l
  rw [Finset.sum_congr rfl fun i _ => h2 i, sum_pairedWalk]
