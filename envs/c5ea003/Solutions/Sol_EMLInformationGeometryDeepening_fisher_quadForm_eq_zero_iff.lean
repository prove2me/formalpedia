-- Prove2me | solution 1 for EMLInformationGeometryDeepening.fisher_quadForm_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:16.141983+00:00
-- url     : https://prove2.me/submissions/002c1f68-3c4e-485a-9e24-67d80b0b2c02

-- Sol generated from Probability/EMLInformationGeometryDeepening.lean
import Mathlib
import Definitions.Def_Probability_EMLInformationGeometryDeepening

/-!
# Exact nullspace geometry for finite exp-log models

This file deepens the finite EML analysis from a single common exponential scale to
an arbitrary feature `g₁`.  It proves a general Gram/nullspace theorem for Fisher
matrices, applies it to the three-parameter exp-log model

`exp(θ₁ g₁(x)) * log(θ₂ g₂(x) + θ₃)`,

and isolates the precise obstruction caused by a constant exponential feature.
The result is stronger than merely exhibiting a zero determinant: every null
Fisher direction is characterized pointwise as a vanishing centered directional
score.
-/

noncomputable section

open Finset
open scoped BigOperators

open EMLInformationGeometryDeepening

variable {ι : Type*} [Fintype ι]
variable {d : ℕ}





















open EMLInformationGeometryDeepening in
theorem solution(p : ι → ℝ) (s : ι → Fin d → ℝ)
    (hp : ∀ i, 0 < p i) (v : Fin d → ℝ) :
    (∑ j, ∑ k, v j * fisherMatrix p s j k * v k) = 0 ↔
      ∀ i, directionalScore p s v i = 0 := by
  have hsum : ∑ j, ∑ k, v j * fisherMatrix p s j k * v k = ∑ i, p i * directionalScore p s v i ^ 2 := by
    simp only [fisherMatrix, directionalScore, pow_two]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    -- First swap the inner sums (k ↔ i), then outer sums (j ↔ i)
    have h₁ : ∀ j, ∑ k, ∑ i, v j * (p i * centeredScore p s i j * centeredScore p s i k) * v k =
              ∑ i, ∑ k, v j * (p i * centeredScore p s i j * centeredScore p s i k) * v k := fun j =>
      Finset.sum_comm
    simp_rw [h₁]
    rw [Finset.sum_comm]
    -- Both sides now have ∑ y : ι, ∑ x : Fin d, ∑ k : Fin d
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro x _
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  -- Now prove: (∑ i, p i * directionalScore p s v i ^ 2) = 0 ↔ ∀ i, directionalScore p s v i = 0
  constructor
  · intro h i
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (le_of_lt (hp j)) (sq_nonneg _))] at h
    specialize h i (Finset.mem_univ i)
    simp only [mul_eq_zero] at h
    rw [← sq_eq_zero_iff]
    exact h.resolve_left (ne_of_gt (hp i))
  · intro h
    simp [h]
