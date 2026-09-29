-- Prove2me | solution 1 for RainbowAP.majority_nonSurjective_of
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:22:10.454684+00:00
-- url     : https://prove2.me/submissions/299175da-7d6a-46b2-bb17-f379478f0bda

-- Sol generated from Shared/RainbowAPSpectrumThreshold.lean
import Mathlib
import Definitions.Def_Shared_RainbowAPSpectrumMoments
import Definitions.Def_Shared_RainbowAPSpectrumThreshold
import Theorems.Thm_RainbowAP_sum_missCount
import Theorems.Thm_RainbowAP_sum_missCount_sq

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

lemma sum_missCount_sq_over_nonSurj_le (m : ℕ) :
    ∑ f ∈ nonSurjSet α m, (missCount f) ^ 2 ≤ ∑ f : Fin m → α, (missCount f) ^ 2 :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ (nonSurjSet α m))

/-- **Second moment (Cauchy–Schwarz) bound** on the number of non-surjective words. -/
lemma sq_sum_missCount_le (m : ℕ) :
    (∑ f : Fin m → α, missCount f) ^ 2
      ≤ nonSurjCount α m * ∑ f : Fin m → α, (missCount f) ^ 2 := by
  calc (∑ f : Fin m → α, missCount f) ^ 2
      = (∑ f ∈ nonSurjSet α m, missCount f) ^ 2 := by rw [sum_missCount_over_nonSurj]
    _ ≤ (nonSurjSet α m).card * ∑ f ∈ nonSurjSet α m, (missCount f) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ nonSurjCount α m * ∑ f : Fin m → α, (missCount f) ^ 2 := by
        exact Nat.mul_le_mul_left _ (sum_missCount_sq_over_nonSurj_le m)








open RainbowAP in
theorem solution(m : ℕ) (hN : 2 ≤ Fintype.card α)
    (h : Fintype.card α ^ m < (Fintype.card α + 1) * (Fintype.card α - 1) ^ m) :
    Fintype.card α ^ m < 2 * nonSurjCount α m := by
  set N := Fintype.card α with hNdef
  obtain ⟨P, hP⟩ : ∃ P, N = P + 2 := ⟨N - 2, by omega⟩
  set A := (N - 1) ^ m with hA
  set B := (N - 2) ^ m with hB
  have hApos : 0 < A := by
    have : 0 < N - 1 := by omega
    exact pow_pos this m
  have hS1 : ∑ f : Fin m → α, missCount f = N * A := sum_missCount m
  have hS2 : ∑ f : Fin m → α, (missCount f) ^ 2 = N * A + N * (N - 1) * B :=
    sum_missCount_sq m
  have hCS : (N * A) ^ 2 ≤ nonSurjCount α m * (N * A + N * (N - 1) * B) := by
    have := sq_sum_missCount_le (α := α) m
    rwa [hS1, hS2] at this
  -- the key arithmetic estimate
  have hNB : N ^ m * B ≤ A ^ 2 := by
    have h1 : N ^ m * B = (N * (N - 2)) ^ m := by
      rw [hB, ← Nat.mul_pow]
    have h2 : A ^ 2 = ((N - 1) * (N - 1)) ^ m := by
      rw [hA, ← pow_mul, mul_comm m 2, pow_mul, sq]
    rw [h1, h2]
    refine Nat.pow_le_pow_left ?_ m
    have hN1 : N - 1 = P + 1 := by omega
    have hN2 : N - 2 = P := by omega
    rw [hN1, hN2, hP]
    nlinarith
  have hNA : N ^ m * A < (N + 1) * A ^ 2 := by
    calc N ^ m * A < ((N + 1) * A) * A := by
          exact Nat.mul_lt_mul_of_lt_of_le h (le_refl A) hApos
      _ = (N + 1) * A ^ 2 := by ring
  have hkey : N ^ m * (N * A + N * (N - 1) * B) < 2 * (N * A) ^ 2 := by
    have expand : N ^ m * (N * A + N * (N - 1) * B)
        = N * (N ^ m * A) + (N * (N - 1)) * (N ^ m * B) := by ring
    have hb : (N * (N - 1)) * (N ^ m * B) ≤ (N * (N - 1)) * A ^ 2 :=
      Nat.mul_le_mul_left _ hNB
    have ha : N * (N ^ m * A) < N * ((N + 1) * A ^ 2) := by
      have hNpos : 0 < N := by omega
      nlinarith [hNA, hNpos]
    have hsum : N * (N ^ m * A) + (N * (N - 1)) * (N ^ m * B)
        < N * ((N + 1) * A ^ 2) + (N * (N - 1)) * A ^ 2 := by omega
    have hfinal : N * ((N + 1) * A ^ 2) + (N * (N - 1)) * A ^ 2 = 2 * (N * A) ^ 2 := by
      have h1 : (N + 1) + (N - 1) = 2 * N := by omega
      calc N * ((N + 1) * A ^ 2) + (N * (N - 1)) * A ^ 2
          = (N * A ^ 2) * ((N + 1) + (N - 1)) := by ring
        _ = (N * A ^ 2) * (2 * N) := by rw [h1]
        _ = 2 * (N * A) ^ 2 := by ring
    omega
  have hS2pos : 0 < N * A + N * (N - 1) * B := by positivity
  nlinarith [hCS, hkey, hS2pos]
