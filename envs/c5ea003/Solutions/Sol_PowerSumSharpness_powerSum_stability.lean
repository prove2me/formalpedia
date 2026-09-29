-- Prove2me | solution 1 for PowerSumSharpness.powerSum_stability
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:16:41.434798+00:00
-- url     : https://prove2.me/submissions/2fd168b9-b9ff-4a52-ae47-ec596283b804

-- Sol generated from Probability/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Probability_PowerSumSharpness
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



/-! ## 2. Power sums of a weight system on `{0, …, N}` -/


lemma powerSum_sub (N : ℕ) (w v : ℕ → ℝ) (k : ℕ) :
    powerSum N w k - powerSum N v k = ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k := by
  rw [powerSum, powerSum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma natCast_injOn (N : ℕ) : Set.InjOn (fun i : ℕ => (i : ℝ)) (range (N + 1)) :=
  fun _ _ _ _ hab => Nat.cast_injective hab


/-! ## 3. The alternating binomial functional -/







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
theorem solution{N : ℕ} {w v : ℕ → ℝ} {eps : ℝ}
    (h : ∀ k ≤ N, |powerSum N w k - powerSum N v k| ≤ eps) :
    ∀ j ≤ N, |w j - v j| ≤ lagrangeWeight N j * eps := by
  intro j hj
  have hjmem : j ∈ range (N + 1) := mem_range.mpr (by omega)
  have hcard : (range (N + 1)).card = N + 1 := card_range _
  have hdeg : (Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).natDegree
      < (range (N + 1)).card := by
    rw [Lagrange.natDegree_basis (natCast_injOn N) hjmem, hcard]
    omega
  have hkey := sum_eval_eq_moment_combination (v := fun i : ℕ => (i : ℝ))
    (d := fun i => w i - v i) hdeg
  rw [Finset.sum_eq_single j] at hkey
  · rw [Lagrange.eval_basis_self (natCast_injOn N) hjmem, mul_one, hcard] at hkey
    simp only at hkey
    rw [hkey]
    calc |∑ k ∈ range (N + 1),
            (Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k *
              ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k|
        ≤ ∑ k ∈ range (N + 1),
            |(Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k *
              ∑ i ∈ range (N + 1), (w i - v i) * (i : ℝ) ^ k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range (N + 1),
            |(Lagrange.basis (range (N + 1)) (fun i : ℕ => (i : ℝ)) j).coeff k| * eps := by
          refine Finset.sum_le_sum fun k hk => ?_
          rw [abs_mul, ← powerSum_sub]
          exact mul_le_mul_of_nonneg_left (h k (Nat.lt_succ_iff.mp (mem_range.mp hk)))
            (abs_nonneg _)
      _ = lagrangeWeight N j * eps := by rw [lagrangeWeight, Finset.sum_mul]
  · intro i hi hij
    rw [Lagrange.eval_basis_of_ne (Ne.symm hij) hi, mul_zero]
  · intro hcon
    exact absurd hjmem hcon
