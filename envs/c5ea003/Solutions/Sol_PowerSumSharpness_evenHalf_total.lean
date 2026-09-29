-- Prove2me | solution 1 for PowerSumSharpness.evenHalf_total
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:00:43.044161+00:00
-- url     : https://prove2.me/submissions/75a26de5-96f5-439d-9825-3141585680db

-- Sol generated from Probability/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
import Theorems.Thm_PowerSumSharpness_alternating_binom_eval
/-
# Sharpness of the finite moment problem on `{0, 1, …, N}`

A "distribution" supported in `{0, 1, …, N}` is here a weight function `w : ℕ → ℝ`
(we only ever look at `w` on `Finset.range (N+1)`), and its *power sums* — the moments —
are `powerSum N w k = ∑ i ≤ N, w i * i ^ k`.

The file proves a complete rigidity/sharpness package.

* **Rigidity (`powerSum_determined`).**  Knowing the power sums for all `k ≤ N`
  determines the weights on `{0, …, N}`.  The proof is a Lagrange-interpolation
  (Vandermonde) argument packaged as `eq_zero_of_moments_zero`, which is stated for an
  arbitrary finite family of pairwise distinct real nodes.
* **Sharpness (`powerSums_not_determined_of_lt`).**  The range `k ≤ N` cannot be
  shortened: for every `K < N` there are two genuine probability distributions on
  `{0, …, N}` whose power sums agree for all `k ≤ K` yet which are different — the even
  and odd halves of the binomial weights `i ↦ C(N,i)/2^{N-1}`.  For `N = 2` this is
  exactly the classical pair `{0,2}` versus `{1,1}` (`multiset_zero_two_ne_one_one`).
* **Structure of the failure (`diff_eq_alternating`).**  The failure is *unique*: any two
  weight systems on `{0, …, N}` whose power sums agree for all `k < N` differ by a scalar
  multiple of the alternating binomial vector `i ↦ (-1)^i C(N,i)`.  Thus the collisions at
  `K = N - 1` form a one-parameter family and there are none at `K = N`.
* **Quantitative gap (`powerSum_gap_at_N`).**  For such a pair the `N`-th power sums differ
  by exactly `c · (-1)^N · N !`, where `c` is the weight discrepancy at the node `0`.
  This rests on the sharp alternating-sum identity `alternating_binom_eval`,
  `∑ i ≤ N, (-1)^i C(N,i) p(i) = (-1)^N N! · [X^N] p` for `deg p ≤ N`, proved by induction
  through a finite-difference (Pascal telescoping) argument.
* **Multiset form (`multiset_determined_by_powerSums`).**  Two multisets of naturals bounded
  by `N` with the same power sums `∑ x^k` for `k ≤ N` are equal.
-/

open Finset Polynomial

open PowerSumSharpness

/-! ## 1. A Vandermonde / Lagrange vanishing principle -/




/-! ## 2. Power sums of a weight system on `{0, …, N}` -/


lemma powerSum_sub (N : ℕ) (w v : ℕ → ℝ) (k : ℕ) :
    powerSum N w k - powerSum N v k = ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k := by
  rw [powerSum, powerSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring



/-! ## 3. The alternating binomial functional -/





/-- The alternating binomial functional annihilates all powers below `N`. -/
theorem alternating_binom_pow_lt {N k : ℕ} (hk : k < N) :
    ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ k = 0 := by
  have hdeg : (X ^ k : ℝ[X]).degree ≤ (N : WithBot ℕ) := by
    rw [Polynomial.degree_X_pow]
    exact_mod_cast Nat.cast_le.mpr hk.le
  have := alternating_binom_eval N (X ^ k) hdeg
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.coeff_X_pow,
    if_neg (by omega : ¬ N = k), mul_zero] at this
  exact this


/-! ## 4. Structure of the moment collisions at order `N - 1` -/





/-! ## 5. The sharpness construction: even and odd binomial halves -/





lemma halves_sub (N i : ℕ) :
    evenHalf N i - oddHalf N i = (-1 : ℝ) ^ i * (N.choose i) / 2 ^ (N - 1) := by
  unfold evenHalf oddHalf
  by_cases h : Even i
  · rw [if_pos h, if_pos h, Even.neg_one_pow h]
    ring
  · rw [if_neg h, if_neg h, Odd.neg_one_pow (Nat.not_even_iff_odd.mp h)]
    ring

lemma halves_add (N i : ℕ) :
    evenHalf N i + oddHalf N i = (N.choose i : ℝ) / 2 ^ (N - 1) := by
  unfold evenHalf oddHalf
  split <;> ring

/-- The two halves have the same power sums in every order below `N`. -/
theorem halves_powerSum_agree {N k : ℕ} (hk : k < N) :
    powerSum N (evenHalf N) k = powerSum N (oddHalf N) k := by
  have := powerSum_sub N (evenHalf N) (oddHalf N) k
  rw [show ∑ i ∈ range (N + 1), (evenHalf N i - oddHalf N i) * (i : ℝ) ^ k
        = (∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ k) / 2 ^ (N - 1) from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [halves_sub]; ring,
    alternating_binom_pow_lt hk, zero_div] at this
  linarith






/-! ## 6. Multiset ("empirical distribution") formulation -/




/-! ## 7. How large must a moment collision be? -/




/-! ## 8. Machine-checked exhaustive search (small cases)

These two statements are the `N = 2` rows of the exhaustive search reported in
`ComputationalEvidence.md`, §8: among sorted tuples with entries in `{0,1,2}`, the pairs
with equal first power sums are exactly the ones predicted by `diff_eq_alternating`, i.e.
those whose count vectors differ by a multiple of `(1, -2, 1)`. -/



/-! ## 9. Extremal separation and stability -/





/-! ## 10. The collision-size bound `2^(N-1)` is attained for every `N` -/












open PowerSumSharpness in
theorem solution{N : ℕ} (hN : 1 ≤ N) : powerSum N (evenHalf N) 0 = 1 := by
  have hsum : powerSum N (evenHalf N) 0 + powerSum N (oddHalf N) 0 = 2 := by
    simp only [powerSum, pow_zero, mul_one]
    rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => halves_add N i), ← Finset.sum_div]
    rw [show ∑ i ∈ range (N + 1), (N.choose i : ℝ) = ((∑ i ∈ range (N + 1), N.choose i : ℕ) : ℝ)
        from by push_cast; rfl, Nat.sum_range_choose]
    rw [show N = (N - 1) + 1 from by omega]
    push_cast
    rw [pow_succ]
    field_simp
  have hagree : powerSum N (evenHalf N) 0 = powerSum N (oddHalf N) 0 :=
    halves_powerSum_agree (by omega)
  linarith
