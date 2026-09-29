-- Prove2me | solution 1 for RainbowAP.majority_surjective_of
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:22:13.188411+00:00
-- url     : https://prove2.me/submissions/1035da3e-2a42-4e67-8ca4-c6cadfb39adb

-- Sol generated from Shared/RainbowAPSpectrumThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_sum_missCount

/-!
# The full-spectrum (coupon-collector) threshold for words over a finite alphabet

For a finite alphabet `α` with `N = |α|` letters, a word `f : Fin m → α` has *full spectrum*
if it is surjective, i.e. every letter of `α` occurs.  We study the counting threshold

  `spectrumThreshold α = least m such that a strict majority of the `N ^ m` words of length `m`
   have full spectrum`.

The two criteria proved here are purely arithmetic and come from the first and second moment
identities of `Shared.RainbowAPSpectrumMoments`:

* if `2 * N * (N-1)^m < N^m` then the majority is surjective (union bound / first moment);
* if `N^m < (N+1) * (N-1)^m` then the majority is **not** surjective
  (Cauchy–Schwarz / second moment).

Both criteria are sharp up to the additive constants inside the logarithm, which is what makes
the resulting threshold asymptotically `N log N`.
-/

open Finset

open RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]



lemma sum_missCount_over_nonSurj (m : ℕ) :
    ∑ f ∈ nonSurjSet α m, missCount f = ∑ f : Fin m → α, missCount f := by
  refine Finset.sum_subset (Finset.subset_univ (nonSurjSet α m)) ?_
  intro f _ hf
  simp only [nonSurjSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt,
    Nat.le_zero] at hf
  exact hf



/-- Each non-surjective word misses at least one letter, so the first moment dominates. -/
lemma nonSurjCount_le (m : ℕ) :
    nonSurjCount α m ≤ Fintype.card α * (Fintype.card α - 1) ^ m := by
  rw [← sum_missCount m]
  calc nonSurjCount α m = ∑ _f ∈ nonSurjSet α m, 1 := by
        simp [nonSurjCount]
    _ ≤ ∑ f ∈ nonSurjSet α m, missCount f := by
        refine Finset.sum_le_sum ?_
        intro f hf
        simp only [nonSurjSet, Finset.mem_filter, Finset.mem_univ, true_and] at hf
        exact hf
    _ = ∑ f : Fin m → α, missCount f := sum_missCount_over_nonSurj m







open RainbowAP in
theorem solution(m : ℕ)
    (h : 2 * Fintype.card α * (Fintype.card α - 1) ^ m < Fintype.card α ^ m) :
    2 * nonSurjCount α m < Fintype.card α ^ m :=
  calc 2 * nonSurjCount α m
      ≤ 2 * (Fintype.card α * (Fintype.card α - 1) ^ m) :=
        Nat.mul_le_mul_left _ (nonSurjCount_le m)
    _ = 2 * Fintype.card α * (Fintype.card α - 1) ^ m := by ring
    _ < Fintype.card α ^ m := h
