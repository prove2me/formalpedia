-- Prove2me | solution 1 for BanditAlgorithm.exists_pointwise_le_of_compact_convex_weighted_le
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T18:25:30.099921+00:00
-- url     : https://prove2.me/submissions/120fa1b9-1208-4188-9994-727597b92b59

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped BigOperators

namespace BanditAlgorithm

noncomputable section

theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {I : Type*} [Fintype I] [Nonempty I]
    (X : Set E) (hXne : X.Nonempty) (hXconv : Convex ℝ X) (hXcomp : IsCompact X)
    (g : E →L[ℝ] (I → ℝ)) (C : ℝ)
    (hweighted : ∀ lam : I → ℝ, lam ∈ stdSimplex ℝ I →
      ∃ x ∈ X, ∑ i : I, lam i * g x i ≤ C) :
    ∃ x ∈ X, ∀ i : I, g x i ≤ C := by
  classical
  let Y : Set (I → ℝ) := stdSimplex ℝ I
  let F : E → (I → ℝ) → ℝ := fun x lam ↦ ∑ i : I, lam i * g x i
  have hYne : Y.Nonempty := by
    let i₀ : I := Classical.choice inferInstance
    refine ⟨fun i ↦ if i = i₀ then 1 else 0, ?_⟩
    constructor
    · intro i
      positivity
    · simp
  have hYconv : Convex ℝ Y := convex_stdSimplex ℝ I
  have hYcomp : IsCompact Y := isCompact_stdSimplex ℝ I
  have hFx_cont : ∀ x ∈ X, ContinuousOn (fun lam ↦ F x lam) Y := by
    intro x hx
    apply Continuous.continuousOn
    dsimp [F]
    fun_prop
  have hFx_conc : ∀ x ∈ X, ConcaveOn ℝ Y (fun lam ↦ F x lam) := by
    intro x hx
    refine ⟨hYconv, ?_⟩
    intro a ha b hb u v hu hv huv
    dsimp [F]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply le_of_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hFy_cont : ∀ lam ∈ Y, ContinuousOn (fun x ↦ F x lam) X := by
    intro lam hlam
    apply Continuous.continuousOn
    dsimp [F]
    fun_prop
  have hFy_conv : ∀ lam ∈ Y, ConvexOn ℝ X (fun x ↦ F x lam) := by
    intro lam hlam
    refine ⟨hXconv, ?_⟩
    intro a ha b hb u v hu hv huv
    dsimp [F]
    rw [map_add, map_smul, map_smul, Finset.mul_sum, Finset.mul_sum]
    apply le_of_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  obtain ⟨x₀, hx₀, lam₀, hlam₀, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn hXne hXconv hXcomp
      (fun lam hlam ↦ (hFy_cont lam hlam).lowerSemicontinuousOn)
      (fun lam hlam ↦ (hFy_conv lam hlam).quasiconvexOn)
      hYconv hYne hYcomp
      (fun x hx ↦ (hFx_cont x hx).upperSemicontinuousOn)
      (fun x hx ↦ (hFx_conc x hx).quasiconcaveOn)
  obtain ⟨x₁, hx₁, hx₁C⟩ := hweighted lam₀ hlam₀
  refine ⟨x₀, hx₀, ?_⟩
  intro i
  let e : I → ℝ := fun j ↦ if j = i then 1 else 0
  have he : e ∈ Y := by
    constructor
    · intro j
      dsimp [e]
      positivity
    · simp [e]
  have hleft := hsaddle x₁ hx₁ e he
  have hxe : F x₀ e = g x₀ i := by
    dsimp [F, e]
    simp
  exact hxe ▸ hleft.trans hx₁C

end
end BanditAlgorithm
