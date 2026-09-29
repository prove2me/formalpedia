-- Prove2me | solution 1 for PowerSumSharpness.powerSum_gap_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:40.183841+00:00
-- url     : https://prove2.me/submissions/b065750a-08d8-4fc9-a068-f4abf0ee1f88

-- Sol generated from Probability/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
import Theorems.Thm_PowerSumSharpness_alternating_binom_eval
import Theorems.Thm_PowerSumSharpness_diff_eq_alternating
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






/-- At the critical order `N` the alternating binomial functional equals `(-1)^N N!`. -/
theorem alternating_binom_pow_self (N : ℕ) :
    ∑ i ∈ range (N + 1), (-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ N
      = (-1 : ℝ) ^ N * (N.factorial : ℝ) := by
  have hdeg : (X ^ N : ℝ[X]).degree ≤ (N : WithBot ℕ) := le_of_eq (Polynomial.degree_X_pow N)
  have := alternating_binom_eval N (X ^ N) hdeg
  simpa using this

/-! ## 4. Structure of the moment collisions at order `N - 1` -/


/-- **Quantitative sharpness.**  Two weight systems on `{0, …, N}` agreeing in all power sums
of order `< N` have `N`-th power sums differing by exactly `(w 0 - v 0) · (-1)^N · N !`. -/
theorem powerSum_gap_at_N {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    powerSum N w N - powerSum N v N = (w 0 - v 0) * ((-1 : ℝ) ^ N * (N.factorial : ℝ)) := by
  rw [powerSum_sub]
  have : ∀ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ N
      = (w 0 - v 0) * ((-1 : ℝ) ^ i * (N.choose i) * (i : ℝ) ^ N) := by
    intro i hi
    rw [diff_eq_alternating h i (by simpa using Nat.lt_succ_iff.mp (mem_range.mp hi))]
    ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, alternating_binom_pow_self]

/-- **Total variation of a moment collision.**  If the power sums agree below order `N`, the
`ℓ¹` distance between the two weight systems is exactly `|w 0 - v 0| · 2^N`. -/
theorem total_variation_eq {N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    ∑ i ∈ range (N + 1), |w i - v i| = |w 0 - v 0| * 2 ^ N := by
  have hterm : ∀ i ∈ range (N + 1), |w i - v i| = |w 0 - v 0| * (N.choose i : ℝ) := by
    intro i hi
    rw [diff_eq_alternating h i (Nat.lt_succ_iff.mp (mem_range.mp hi)), abs_mul, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  congr 1
  rw [show ∑ i ∈ range (N + 1), (N.choose i : ℝ) = ((∑ i ∈ range (N + 1), N.choose i : ℕ) : ℝ)
      from by push_cast; rfl, Nat.sum_range_choose]
  push_cast
  rfl


/-! ## 5. The sharpness construction: even and odd binomial halves -/













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
theorem solution{N : ℕ} (hN : 1 ≤ N) {w v : ℕ → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hw1 : powerSum N w 0 = 1) (hv1 : powerSum N v 0 = 1)
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    |powerSum N w N - powerSum N v N| ≤ (N.factorial : ℝ) / 2 ^ (N - 1) := by
  have htv := total_variation_eq h
  have hdom : ∑ i ∈ range (N + 1), |w i - v i| ≤ ∑ i ∈ range (N + 1), (w i + v i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rcases abs_cases (w i - v i) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
      linarith [hw i, hv i]
  have hmass : ∑ i ∈ range (N + 1), (w i + v i) = 2 := by
    have h1 : ∑ i ∈ range (N + 1), w i = 1 := by simpa [powerSum] using hw1
    have h2 : ∑ i ∈ range (N + 1), v i = 1 := by simpa [powerSum] using hv1
    rw [Finset.sum_add_distrib, h1, h2]
    norm_num
  have hc : |w 0 - v 0| * 2 ^ N ≤ 2 := by rw [← htv]; linarith
  have hpow : (2 : ℝ) ^ N = 2 * 2 ^ (N - 1) := by
    nth_rewrite 1 [show N = (N - 1) + 1 from by omega]
    rw [pow_succ]; ring
  have hc' : |w 0 - v 0| * 2 ^ (N - 1) ≤ 1 := by rw [hpow] at hc; linarith
  have hgap : |powerSum N w N - powerSum N v N| = |w 0 - v 0| * (N.factorial : ℝ) := by
    rw [powerSum_gap_at_N h, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      Nat.abs_cast]
  rw [hgap, le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (N - 1))]
  have hfac : (0 : ℝ) ≤ (N.factorial : ℝ) := by positivity
  nlinarith
