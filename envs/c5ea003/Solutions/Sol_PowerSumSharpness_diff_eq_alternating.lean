-- Prove2me | solution 1 for PowerSumSharpness.diff_eq_alternating
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:17.690123+00:00
-- url     : https://prove2.me/submissions/15dc15ce-61d4-4f54-a279-0d4c0df2d236

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

/-- The `d`-weighted value of a polynomial of degree `< s.card` at the nodes `v i` is the
corresponding combination of the `d`-weighted moments. -/
theorem sum_eval_eq_moment_combination {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    {d : ι → ℝ} {p : ℝ[X]} (hp : p.natDegree < s.card) :
    ∑ i ∈ s, d i * p.eval (v i)
      = ∑ k ∈ Finset.range s.card, p.coeff k * ∑ i ∈ s, d i * v i ^ k := by
  have hrw : ∀ i ∈ s, d i * p.eval (v i)
      = ∑ k ∈ Finset.range s.card, p.coeff k * (d i * v i ^ k) := by
    intro i _
    rw [Polynomial.eval_eq_sum_range' hp, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [Finset.sum_congr rfl hrw, Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]

/-- If the `d`-weighted moments of the nodes `v i` vanish up to order `s.card - 1`, then the
`d`-weighted value of *every* polynomial of degree `< s.card` vanishes. -/
theorem sum_eval_eq_zero_of_moments_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    {d : ι → ℝ} (h : ∀ k < s.card, ∑ i ∈ s, d i * v i ^ k = 0)
    {p : ℝ[X]} (hp : p.natDegree < s.card) :
    ∑ i ∈ s, d i * p.eval (v i) = 0 := by
  rw [sum_eval_eq_moment_combination hp]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [h k (Finset.mem_range.mp hk), mul_zero]

/-- **Vandermonde vanishing.**  A weight system on `s.card` pairwise distinct real nodes
whose moments of orders `0, 1, …, s.card - 1` all vanish is identically zero.  This is the
invertibility of the Vandermonde matrix, obtained here from Lagrange interpolation. -/
theorem eq_zero_of_moments_zero {ι : Type*} [DecidableEq ι] {s : Finset ι} {v : ι → ℝ}
    (hv : Set.InjOn v s) {d : ι → ℝ}
    (h : ∀ k < s.card, ∑ i ∈ s, d i * v i ^ k = 0) : ∀ j ∈ s, d j = 0 := by
  intro j hj
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨j, hj⟩
  have hdeg : (Lagrange.basis s v j).natDegree < s.card := by
    rw [Lagrange.natDegree_basis hv hj]; omega
  have key := sum_eval_eq_zero_of_moments_zero h hdeg
  rw [Finset.sum_eq_single j] at key
  · rwa [Lagrange.eval_basis_self hv hj, mul_one] at key
  · intro i hi hij
    rw [Lagrange.eval_basis_of_ne (Ne.symm hij) hi, mul_zero]
  · intro hc; exact absurd hj hc

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
theorem solution{N : ℕ} {w v : ℕ → ℝ}
    (h : ∀ k < N, powerSum N w k = powerSum N v k) :
    ∀ i ≤ N, w i - v i = (w 0 - v 0) * ((-1 : ℝ) ^ i * (N.choose i)) := by
  set e : ℕ → ℝ := fun j => (w j - v j) - (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) with he
  have he0 : e 0 = 0 := by simp [he]
  have hsum : ∀ k < N, ∑ j ∈ range (N + 1), e j * (j : ℝ) ^ k = 0 := by
    intro k hk
    have h1 : ∑ j ∈ range (N + 1), (w j - v j) * (j : ℝ) ^ k = 0 := by
      rw [← powerSum_sub, h k hk, sub_self]
    have h2 : ∑ j ∈ range (N + 1),
        (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k = 0 := by
      have hfac : ∑ j ∈ range (N + 1), (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k
          = (w 0 - v 0) * ∑ j ∈ range (N + 1), (-1 : ℝ) ^ j * (N.choose j) * (j : ℝ) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hfac, alternating_binom_pow_lt hk, mul_zero]
    have h3 : ∑ j ∈ range (N + 1), e j * (j : ℝ) ^ k
        = (∑ j ∈ range (N + 1), (w j - v j) * (j : ℝ) ^ k)
          - ∑ j ∈ range (N + 1), (w 0 - v 0) * ((-1 : ℝ) ^ j * (N.choose j)) * (j : ℝ) ^ k := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by simp only [he]; ring
    rw [h3, h1, h2, sub_zero]
  -- the shifted nodes `1, …, N` carry `N` moment conditions, so the tail of `e` vanishes
  have hshift : ∀ k < (range N).card,
      ∑ i ∈ range N, e (i + 1) * ((fun i : ℕ => ((i + 1 : ℕ) : ℝ)) i) ^ k = 0 := by
    intro k hk
    rw [card_range] at hk
    have := hsum k hk
    rw [Finset.sum_range_succ' (fun j => e j * (j : ℝ) ^ k) N, he0, zero_mul, add_zero] at this
    exact this
  have hinj : Set.InjOn (fun i : ℕ => ((i + 1 : ℕ) : ℝ)) (range N) := by
    intro a _ b _ hab
    have : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := hab
    have := Nat.cast_injective this
    omega
  have htail := eq_zero_of_moments_zero hinj hshift
  intro i hi
  match i with
  | 0 => simp
  | (m + 1) =>
      have := htail m (mem_range.mpr (by omega))
      simp only [he] at this
      linarith
