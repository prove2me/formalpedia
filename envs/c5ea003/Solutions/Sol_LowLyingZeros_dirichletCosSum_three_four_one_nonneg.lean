-- Prove2me | solution 1 for LowLyingZeros.dirichletCosSum_three_four_one_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:47:51.914157+00:00
-- url     : https://prove2.me/submissions/980e8968-6641-44c0-a19e-96a7b79e7836

-- Sol generated from Speculative/NumberTheory/LowLyingZeros.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_LowLyingZeros

/-!
# Explicit bounds on low-lying zeros of automorphic L-functions

This file formalizes, in an abstract but faithful form, the two analytic pillars that
underlie explicit results on the low-lying zeros of automorphic `L`-functions.

## The de la Vallée Poussin positivity

Every classical proof of a zero-free region for an `L`-function — and hence every
explicit statement that its low-lying zeros stay away from the line `ℜ(s) = 1`, pushing
them towards the critical line `ℜ(s) = 1/2` — rests on the elementary trigonometric
inequality
`3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`.
Applied to a Dirichlet series `log L(s) = ∑ b_n λ_n^{-s}` with **nonnegative** coefficients
(the situation for `ζ`, for `L`-functions of self-dual cuspidal representations, and for
symmetric-power `L`-functions on the edge of the critical strip), it gives the positivity
`3 · A(σ,0) + 4 · A(σ,t) + A(σ,2t) ≥ 0`, which forbids a zero on `ℜ(s)=1`.

We prove this positivity for an arbitrary finite nonnegative Dirichlet cosine sum
`dirichletCosSum` (`dirichletCosSum_three_four_one_nonneg`), together with the exact
trinomial identity (`three_four_one_cos`) and its sharp equality case
(`three_four_one_cos_eq_zero_iff`).

## Functional-equation symmetry about the critical line

The completed `L`-function of an automorphic representation satisfies a functional equation
of the shape `Λ(s) = ε · conj (Λ(1 - conj s))` with `|ε| = 1`.  The map
`s ↦ 1 - conj s` is precisely the reflection of the complex plane across the critical line
`ℜ(s) = 1/2`.  Consequently the zero set of `Λ` is symmetric under this reflection, its
fixed points are exactly the points on the critical line, and every zero off the critical
line occurs in a genuine mirror pair of two distinct zeros.

* `critical_reflection_involutive` — `s ↦ 1 - conj s` is an involution.
* `critical_reflection_fixed_iff` — its fixed points are exactly `{s : ℜ s = 1/2}`.
* `zero_reflect_iff` — `Λ s = 0 ↔ Λ (1 - conj s) = 0`.
* `offcritical_zero_pair` — an off-line zero forces a distinct mirror zero.

Together these give a rigorous, self-contained account of *why* the nontrivial zeros of an
automorphic `L`-function are symmetric about `ℜ(s)=1/2` and *why* the positivity method
keeps the low-lying ones off the edge of the critical strip.
-/

open LowLyingZeros

open Finset Real

/-! ## The de la Vallée Poussin trinomial -/

/-- The de la Vallée Poussin identity `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)²`. -/
theorem three_four_one_cos (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) = 2 * (1 + Real.cos θ) ^ 2 := by
  rw [Real.cos_two_mul]; ring

/-- The de la Vallée Poussin positivity `3 + 4 cos θ + cos 2θ ≥ 0`. -/
theorem three_four_one_cos_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  rw [three_four_one_cos]; positivity


/-! ## Nonnegative Dirichlet cosine sums -/


variable {ι : Type*} (F : Finset ι) (a r φ : ι → ℝ)



/-! ## Functional-equation symmetry about the critical line -/









open LowLyingZeros in
theorem solution(σ t : ℝ)
    (hr : ∀ n ∈ F, 0 < r n) (ha : ∀ n ∈ F, 0 ≤ a n) :
    0 ≤ 3 * dirichletCosSum F a r φ σ 0
        + 4 * dirichletCosSum F a r φ σ t
        + dirichletCosSum F a r φ σ (2 * t) := by
  have key :
      3 * dirichletCosSum F a r φ σ 0
        + 4 * dirichletCosSum F a r φ σ t
        + dirichletCosSum F a r φ σ (2 * t)
      = ∑ n ∈ F, a n * r n ^ (-σ) *
          (3 + 4 * Real.cos (t * φ n) + Real.cos (2 * (t * φ n))) := by
    unfold dirichletCosSum
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have h0 : Real.cos (0 * φ n) = 1 := by simp
    have h2 : (2 * t) * φ n = 2 * (t * φ n) := by ring
    rw [h0, h2]; ring
  rw [key]
  apply Finset.sum_nonneg
  intro n hn
  have hrp : (0 : ℝ) ≤ r n ^ (-σ) := le_of_lt (Real.rpow_pos_of_pos (hr n hn) _)
  have htri : 0 ≤ 3 + 4 * Real.cos (t * φ n) + Real.cos (2 * (t * φ n)) :=
    three_four_one_cos_nonneg (t * φ n)
  have hae : 0 ≤ a n := ha n hn
  positivity
