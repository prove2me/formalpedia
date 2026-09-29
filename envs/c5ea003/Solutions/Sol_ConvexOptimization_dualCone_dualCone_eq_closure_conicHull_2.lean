-- Prove2me | solution 2 for ConvexOptimization.dualCone_dualCone_eq_closure_conicHull
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-08-15T14:56:30.503177+00:00
-- url     : https://prove2.me/submissions/18d445b1-62c8-4a6d-aa9b-2099ebda7550

import Mathlib
import Definitions.Def_dualCone
import Definitions.Def_conicHull

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace BipolarAux

open ConvexOptimization

variable {n : ℕ}

theorem zero_mem_conicHull (K : Set (EuclideanSpace ℝ (Fin n))) :
    (0 : EuclideanSpace ℝ (Fin n)) ∈ conicHull K :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

theorem subset_conicHull (K : Set (EuclideanSpace ℝ (Fin n))) : K ⊆ conicHull K := fun x hx =>
  ⟨1, fun _ => 1, fun _ => x, fun _ => zero_le_one, fun _ => hx, by simp⟩

theorem smul_mem_conicHull {K : Set (EuclideanSpace ℝ (Fin n))} {t : ℝ} (ht : 0 ≤ t)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ conicHull K) : t • z ∈ conicHull K := by
  obtain ⟨m, θ, u, hθ, hu, rfl⟩ := hz
  refine ⟨m, fun i => t * θ i, u, fun i => mul_nonneg ht (hθ i), hu, ?_⟩
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]

theorem add_mem_conicHull {K : Set (EuclideanSpace ℝ (Fin n))} {z w : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ conicHull K) (hw : w ∈ conicHull K) : z + w ∈ conicHull K := by
  obtain ⟨m₁, θ₁, u₁, hθ₁, hu₁, rfl⟩ := hz
  obtain ⟨m₂, θ₂, u₂, hθ₂, hu₂, rfl⟩ := hw
  refine ⟨m₁ + m₂, Fin.append θ₁ θ₂, Fin.append u₁ u₂, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hθ₁, hθ₂]
  · intro i
    refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [hu₁, hu₂]
  · rw [Fin.sum_univ_add]
    simp

theorem convex_conicHull (K : Set (EuclideanSpace ℝ (Fin n))) : Convex ℝ (conicHull K) :=
  fun _ hz _ hw _ _ hs ht _ =>
    add_mem_conicHull (smul_mem_conicHull hs hz) (smul_mem_conicHull ht hw)

theorem smul_mem_closure {K : Set (EuclideanSpace ℝ (Fin n))} {t : ℝ} (ht : 0 ≤ t)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ closure (conicHull K)) :
    t • z ∈ closure (conicHull K) := by
  have hmaps : Set.MapsTo (fun x : EuclideanSpace ℝ (Fin n) => t • x) (conicHull K) (conicHull K) :=
    fun _ hx => smul_mem_conicHull ht hx
  exact hmaps.closure (continuous_const_smul t) hz

end BipolarAux

open ConvexOptimization in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    dualCone (dualCone K) = closure (conicHull K) := by
  refine Set.Subset.antisymm ?_ ?_
  · -- `K** ⊆ cl (cone K)`: separate a point outside the closed convex cone.
    intro z hz
    by_contra hzn
    obtain ⟨f, u, hfC, hfz⟩ := geometric_hahn_banach_closed_point
      ((BipolarAux.convex_conicHull K).closure) isClosed_closure hzn
    have h0 : (0 : ℝ) < u := by
      have := hfC 0 (subset_closure (BipolarAux.zero_mem_conicHull K))
      simpa using this
    -- A linear functional bounded above on a cone is nonpositive on it.
    have hfnonpos : ∀ x ∈ closure (conicHull K), f x ≤ 0 := by
      intro x hx
      by_contra hcon
      push_neg at hcon
      have hscale : (u / f x) • x ∈ closure (conicHull K) :=
        BipolarAux.smul_mem_closure (le_of_lt (div_pos h0 hcon)) hx
      have hlt := hfC _ hscale
      rw [ContinuousLinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hcon)] at hlt
      exact lt_irrefl u hlt
    -- Riesz representation of `-f` is a dual vector separating `z`.
    set w : EuclideanSpace ℝ (Fin n) :=
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f with hwdef
    have hw : ∀ x : EuclideanSpace ℝ (Fin n), ⟪w, x⟫ = f x := fun x => by
      rw [hwdef, InnerProductSpace.toDual_symm_apply]
    have hyK : (-w) ∈ dualCone K := by
      intro x hx
      have hxC : x ∈ closure (conicHull K) :=
        subset_closure (BipolarAux.subset_conicHull K hx)
      have := hfnonpos x hxC
      rw [real_inner_comm, inner_neg_left, hw]
      linarith
    have hcontra := hz (-w) hyK
    rw [inner_neg_left, hw] at hcontra
    linarith
  · -- `cl (cone K) ⊆ K**`: every dual vector is nonnegative on the cone, hence on its closure.
    intro z hz w hw
    have hclosed : IsClosed {v : EuclideanSpace ℝ (Fin n) | 0 ≤ ⟪w, v⟫} := by
      have : Continuous fun v : EuclideanSpace ℝ (Fin n) => ⟪w, v⟫ := (innerSL ℝ w).continuous
      exact isClosed_le continuous_const this
    have hsub : conicHull K ⊆ {v : EuclideanSpace ℝ (Fin n) | 0 ≤ ⟪w, v⟫} := by
      rintro _ ⟨m, θ, u, hθ, hu, rfl⟩
      simp only [Set.mem_setOf_eq, inner_sum, real_inner_smul_right]
      refine Finset.sum_nonneg fun i _ => mul_nonneg (hθ i) ?_
      have := hw (u i) (hu i)
      rwa [real_inner_comm] at this
    exact (hclosed.closure_subset_iff.mpr hsub) hz
