-- Prove2me | solution 1 for AdjSum.trace_adjMat_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:39:17.025527+00:00
-- url     : https://prove2.me/submissions/6695127c-f190-48c0-b810-13177f9f1ff1

-- Sol generated from Applications/AdjacentSumPolytopes/TraceMoments.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Necklace
import Theorems.Thm_AdjSum_adjMat_apply

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

lemma sum_range_succ_id (n : ℕ) : ∑ i ∈ Finset.range n, (i + 1) = Nat.choose (n + 1) 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ (k + 1) 1]
    simp [Nat.choose_one_right]
    omega


lemma filter_add_le (s a : ℕ) :
    (Finset.range (s + 1)).filter (fun b => a + b ≤ s) = Finset.range (s + 1 - a) := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_range]
  omega





open AdjSum in
theorem solution(s : ℕ) : Matrix.trace (adjMat s ^ 2) = Nat.choose (s + 2) 2 := by
  have hentry : Matrix.trace (adjMat s ^ 2)
      = ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
          (if (a : ℕ) + (b : ℕ) ≤ s then 1 else 0) := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Matrix.diag_apply, pow_two, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [adjMat_apply, adjMat_apply]
    by_cases h : (a : ℕ) + (b : ℕ) ≤ s
    · have h' : (b : ℕ) + (a : ℕ) ≤ s := by omega
      simp [h, h']
    · have h' : ¬((b : ℕ) + (a : ℕ) ≤ s) := by omega
      simp [h, h']
  rw [hentry]
  have hrange : ∑ a : Fin (s + 1), ∑ b : Fin (s + 1),
      (if (a : ℕ) + (b : ℕ) ≤ s then 1 else 0)
      = ∑ a ∈ Finset.range (s + 1), ∑ b ∈ Finset.range (s + 1),
          (if a + b ≤ s then 1 else 0) := by
    rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin (s + 1),
      (if a + (b : ℕ) ≤ s then 1 else 0))]
    exact Finset.sum_congr rfl (fun a _ =>
      Fin.sum_univ_eq_sum_range (fun b => if a + b ≤ s then 1 else 0) (s + 1))
  rw [hrange]
  have hinner : ∀ a ∈ Finset.range (s + 1),
      ∑ b ∈ Finset.range (s + 1), (if a + b ≤ s then 1 else 0) = s + 1 - a := by
    intro a _
    have hcard : ∑ b ∈ Finset.range (s + 1), (if a + b ≤ s then 1 else 0)
        = ((Finset.range (s + 1)).filter (fun b => a + b ≤ s)).card := by
      rw [Finset.card_filter]
    rw [hcard, filter_add_le, Finset.card_range]
  rw [Finset.sum_congr rfl hinner]
  have hrefl := Finset.sum_range_reflect (fun a => s + 1 - a) (s + 1)
  have hcongr : ∑ a ∈ Finset.range (s + 1), (s + 1 - (s + 1 - 1 - a))
      = ∑ a ∈ Finset.range (s + 1), (a + 1) := by
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_range] at ha
    omega
  rw [hrefl.symm.trans (by rw [hcongr]), sum_range_succ_id]
