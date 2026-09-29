-- Prove2me | solution 1 for RademacherWigner.trace_W_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T15:33:05.775242+00:00
-- url     : https://prove2.me/submissions/808fa8c2-e976-4d0a-a1aa-f75398e7e257

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

theorem entry_diag (g : Config N) (i : Fin N) : entry g i i = 0 := by simp [entry]

theorem entry_mul_self (g : Config N) {i j : Fin N} (h : i ≠ j) :
    entry g i j * entry g i j = 1 := by
  simp [entry, h]




/-! ### The second spectral moment is deterministic -/


/-! ### Expectation over the ensemble -/






/-! ### The sign-flip involution -/



/-! ### The fourth moment -/






















open RademacherWigner in
theorem solution(g : Config N) : ((W g) ^ 2).trace = (N : ℝ) ^ 2 - N := by
  have h : ((W g) ^ 2).trace = ∑ i : Fin N, ∑ j : Fin N, entry g i j * entry g j i := by
    rw [pow_two, Matrix.trace_mul_comm]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, W]
  rw [h]
  have h2 : ∀ i : Fin N, (∑ j : Fin N, entry g i j * entry g j i) = (N : ℝ) - 1 := by
    intro i
    have : ∀ j : Fin N, entry g i j * entry g j i = if j = i then 0 else 1 := by
      intro j
      by_cases hj : j = i
      · simp [hj, entry_diag]
      · rw [entry_symm g i j, entry_mul_self g hj]
        simp [hj]
    rw [Finset.sum_congr rfl fun j _ => this j]
    have hN : 1 ≤ N := lt_of_le_of_lt (Nat.zero_le i) i.isLt
    simp [Finset.sum_ite, Finset.filter_ne', Nat.cast_sub hN]
  rw [Finset.sum_congr rfl fun i _ => h2 i]
  simp
  ring
