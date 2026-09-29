-- Prove2me | solution 1 for EMLInformationGeometryDeepening.constant_feature_forces_fisher_degeneracy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:14.954045+00:00
-- url     : https://prove2.me/submissions/5a17f04a-e31d-458f-9db4-a6ac508a516d

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











omit [Fintype ι] in
/-- If every log argument exceeds one, every unnormalized EML weight is positive. -/
theorem emlRaw_pos (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ)
    (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) (i : ι) :
    0 < emlRaw g₁ g₂ θ i := by
  unfold emlRaw
  apply mul_pos
  · exact Real.exp_pos _
  · exact Real.log_pos (hlog i)

/-- On a nonempty finite sample space, the EML partition function is positive. -/
theorem emlMass_pos [Nonempty ι] (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ)
    (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) :
    0 < emlMass g₁ g₂ θ := by
  unfold emlMass
  apply Finset.sum_pos'
  · intro i _
    exact le_of_lt (emlRaw_pos g₁ g₂ θ hlog i)
  · exact ⟨Classical.arbitrary ι, Finset.mem_univ _, emlRaw_pos g₁ g₂ θ hlog _⟩


/-- The normalized EML weights sum to one. -/
theorem emlProbability_sum [Nonempty ι] (g₁ g₂ : ι → ℝ) (θ : Fin 3 → ℝ)
    (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) :
    ∑ i, emlProbability g₁ g₂ θ i = 1 := by
  unfold emlProbability emlMass
  rw [← Finset.sum_div]
  have hne : ∑ i, emlRaw g₁ g₂ θ i ≠ 0 := ne_of_gt (emlMass_pos g₁ g₂ θ hlog)
  rw [div_self hne]







open EMLInformationGeometryDeepening in
theorem solution[Nonempty ι]
    (g₁ g₂ : ι → ℝ) (c : ℝ) (hg₁ : ∀ i, g₁ i = c)
    (θ : Fin 3 → ℝ) (hlog : ∀ i, 1 < θ 1 * g₂ i + θ 2) :
    let e₁ : Fin 3 → ℝ := fun j => if j = 0 then 1 else 0
    e₁ ≠ 0 ∧
      (∑ j, ∑ k, e₁ j * emlFisher g₁ g₂ θ j k * e₁ k) = 0 := by
  have he₁_ne_zero : (fun j : Fin 3 => if j = 0 then (1 : ℝ) else 0) ≠ 0 := by
    intro h
    have := congr_fun h 0
    simp at this
  have h_quadratic : ∑ j, ∑ k, (fun j => if j = 0 then (1 : ℝ) else 0) j * emlFisher g₁ g₂ θ j k * (fun j => if j = 0 then (1 : ℝ) else 0) k = emlFisher g₁ g₂ θ 0 0 := by
    simp
  constructor
  · exact he₁_ne_zero
  · rw [h_quadratic]
    unfold emlFisher
    simp only [fisherMatrix]
    have h_centered_zero : ∀ i, centeredScore (emlProbability g₁ g₂ θ) (emlRawScore g₁ g₂ θ) i 0 = 0 := by
      intro i
      unfold centeredScore emlRawScore
      simp_rw [hg₁]
      rw [← Finset.sum_mul]
      simp [emlProbability_sum g₁ g₂ θ hlog]
    simp_rw [h_centered_zero]
    simp
