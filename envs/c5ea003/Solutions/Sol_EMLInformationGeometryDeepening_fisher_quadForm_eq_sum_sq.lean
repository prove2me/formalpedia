-- Prove2me | solution 1 for EMLInformationGeometryDeepening.fisher_quadForm_eq_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:15.536003+00:00
-- url     : https://prove2.me/submissions/8ffb9dd8-2c2b-484e-bfb6-4b2c3547bfba

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
    (v : Fin d → ℝ) :
    (∑ j, ∑ k, v j * fisherMatrix p s j k * v k) =
      ∑ i, p i * directionalScore p s v i ^ 2 := by
  unfold fisherMatrix directionalScore
  simp_rw [sq, Finset.mul_sum, Finset.sum_mul]
  simp_rw [mul_assoc, mul_comm, mul_left_comm]
  rw [Finset.sum_comm, Finset.sum_comm, Finset.sum_comm]
  conv_rhs =>
    arg 2
    ext x
    arg 2
    ext x_1
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext y; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  ac_rfl
