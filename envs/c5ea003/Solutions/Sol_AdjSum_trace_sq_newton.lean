-- Prove2me | solution 1 for AdjSum.trace_sq_newton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:44:01.838289+00:00
-- url     : https://prove2.me/submissions/8ac8f5a3-9afd-47fb-8ca0-68aafcf299ce

-- Sol generated from Applications/AdjacentSumPolytopes/TraceMoments.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Theorems.Thm_AdjSum_trace_adjMat
import Theorems.Thm_AdjSum_trace_adjMat_sq

/-!
# The second trace moment and the Newton coefficient `e₂`

`Necklace.trace_adjMat` computed the first trace moment, `tr(A) = ⌊s/2⌋ + 1`, which is the
`m = 1` coefficient of the characteristic polynomial.  This file computes the second
moment exactly,

`tr(A²) = C(s+2, 2)`,

i.e. the number of cyclic adjacent-sum lattice points of length `2` is a triangular
number, and derives the second elementary symmetric function of the spectrum in closed
form via Newton's identity `2e₂ = e₁² − p₂`:

`e₂ = − C(⌊(s+3)/2⌋, 2)`.

This is the `m = 2` instance of the binomial conjecture recorded in `FUTURE_DIRECTIONS.md`
(coefficient of `x^{s+1−m}` in `det(xI − A)` equals
`(−1)^{⌊(m+1)/2⌋} C(⌊(s+1+m)/2⌋, m)`); the `m = 0, 1` instances are `1` and `−tr(A)`, both
already proved.

## Main results

* `AdjSum.trace_adjMat_sq` : `tr(A²) = C(s+2, 2)`.
* `AdjSum.cycCount_one_eq_choose` : the length-`2` cyclic count is `C(s+2, 2)`.
* `AdjSum.trace_sq_newton` : `tr(A²) = tr(A)² + 2·C(⌊(s+3)/2⌋, 2)`, the Newton relation
  that pins down `e₂`.

-- !-- Lab Notes -- !--
* **Experiment.** `tr(A²)` for `s = 0..9` is `1, 3, 6, 10, 15, 21, 28, 36, 45, 55`, exactly
  the triangular numbers `C(s+2,2)`; `tr(A)` is `1, 1, 2, 2, 3, 3, 4, 4, 5, 5`, and the
  differences `tr(A²) − tr(A)²` are `0, 2, 2, 6, 6, 12, 12, 20, 20, 30`, i.e.
  `2·C(⌊(s+3)/2⌋, 2)`.
* **Analysis.** The parity-dependent floor in `e₂` is the first place where the two parity
  classes of the model separate at the level of the characteristic polynomial, which is
  why the conjectured coefficient formula needs `⌊(s+1+m)/2⌋` rather than a polynomial in
  `s`.
* **Critique.** The identity is proved as a natural-number identity, so no division is
  hidden: `Nat.choose` is used instead of `(s+1)(s+2)/2`, and the parity split is
  discharged by `omega` after `Nat.choose_two_right`.
-/

open AdjSum

open Finset


lemma two_mul_choose_two (n : ℕ) : 2 * Nat.choose n 2 = n * (n - 1) := by
  cases n with
  | zero => simp
  | succ m =>
    rw [Nat.choose_two_right, Nat.succ_sub_one]
    obtain ⟨c, hc⟩ : Even ((m + 1) * m) := by
      simpa [mul_comm] using Nat.even_mul_succ_self m
    rw [hc]
    omega






open AdjSum in
theorem solution(s : ℕ) :
    Matrix.trace (adjMat s ^ 2)
      = (Matrix.trace (adjMat s)) ^ 2 + 2 * Nat.choose ((s + 3) / 2) 2 := by
  rw [trace_adjMat_sq, trace_adjMat]
  rcases Nat.even_or_odd s with ⟨k, hk⟩ | ⟨k, hk⟩
  · subst hk
    have h1 : (k + k) / 2 = k := by omega
    have h2 : (k + k + 3) / 2 = k + 1 := by omega
    rw [h1, h2]
    refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
    have e1 : 2 * Nat.choose (k + k + 2) 2 = (k + k + 2) * (k + k + 1) := by
      rw [two_mul_choose_two]
      congr 1
    have e2 : 2 * (2 * Nat.choose (k + 1) 2) = 2 * ((k + 1) * k) := by
      rw [two_mul_choose_two]
      congr 2
    rw [Nat.mul_add, e1, e2]
    ring
  · subst hk
    have h1 : (2 * k + 1) / 2 = k := by omega
    have h2 : (2 * k + 1 + 3) / 2 = k + 2 := by omega
    rw [h1, h2]
    refine Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) ?_
    have e1 : 2 * Nat.choose (2 * k + 1 + 2) 2 = (2 * k + 3) * (2 * k + 2) := by
      rw [two_mul_choose_two]
      congr 1
    have e2 : 2 * (2 * Nat.choose (k + 2) 2) = 2 * ((k + 2) * (k + 1)) := by
      rw [two_mul_choose_two]
      congr 2
    rw [Nat.mul_add, e1, e2]
    ring
