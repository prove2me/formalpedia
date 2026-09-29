-- Prove2me | solution 1 for mme_basis_projected_family_restrict
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T14:26:43.116825+00:00
-- url     : https://prove2.me/submissions/c17808db-8a72-4b68-9130-d5265fc9a059

import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME Module PiTensorProduct BigOperators
universe u
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem rejected_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (keep : ∀ i, I i → Prop)
    (i : Fin 3) (x : I i) (hx : ¬ keep i x) :
    (T.basisAllAllowedGrading b keep).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne
    (T.basisAllAllowedGrading b keep) i 0 1 (by decide)
  exact Submodule.subset_span ⟨x, by simp [hx], rfl⟩

private theorem nested_projection
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) (parent child : ∀ i, I i → Prop)
    (hsub : ∀ i x, child i x → parent i x) (i : Fin 3) :
    ((T.basisAllAllowedGrading b child).blockProj i 0).comp
      (((T.basisAllAllowedGrading b parent).classOf i 0).subtype.comp
        ((T.basisAllAllowedGrading b parent).blockProj i 0)) =
      (T.basisAllAllowedGrading b child).blockProj i 0 := by
  classical
  apply (b i).ext
  intro x
  simp only [LinearMap.comp_apply]
  by_cases hx : parent i x
  · have hm : b i x ∈ (T.basisAllAllowedGrading b parent).classOf i 0 :=
      Submodule.subset_span ⟨x, by simp [hx], rfl⟩
    rw [TensorObj.TypeGrading.blockProj_apply_mem _ i 0 _ hm]
    rfl
  · rw [rejected_projection T b parent i x hx, map_zero, map_zero,
      rejected_projection T b child i x (fun hc ↦ hx (hsub i x hc))]

/-- Coordinate support separation survives an existing parent projection. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {k : ℕ}
    {I : Fin 3 → Type u} [∀ i, Fintype (I i)]
    (b : ∀ i, Basis (I i) K (T.V i))
    (parent : ∀ i, I i → Prop) (keep : Fin k → ∀ i, I i → Prop)
    (hsub : ∀ j i x, keep j i x → parent i x)
    (hunique : ∀ (x : ∀ i, I i) (js : Fin 3 → Fin k),
      (Basis.piTensorProduct b).repr T.t x ≠ 0 →
      (∀ i, keep (js i) i (x i)) → ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun j ↦ T.basisAllAllowedSubtensor b (keep j)))
      (T.basisAllAllowedSubtensor b parent) := by
  classical
  let P := T.basisAllAllowedSubtensor b parent
  let G := T.basisAllAllowedGrading b parent
  let B := fun j ↦ T.basisAllAllowedSubtensor b (keep j)
  let f : ∀ j, ∀ i, T.V i →ₗ[K] (B j).V i :=
    fun j i ↦ (T.basisAllAllowedGrading b (keep j)).blockProj i 0
  let g : ∀ j, ∀ i, P.V i →ₗ[K] (B j).V i :=
    fun j i ↦ (f j i).comp (G.classOf i 0).subtype
  have hcomp (j i) : (g j i).comp (G.blockProj i 0) = f j i := by
    simpa only [g, LinearMap.comp_assoc] using nested_projection T b parent (keep j) (hsub j) i
  have hmap (js : Fin 3 → Fin k) :
      PiTensorProduct.map (fun i ↦ g (js i) i) P.t =
        PiTensorProduct.map (fun i ↦ f (js i) i) T.t := by
    change PiTensorProduct.map (fun i ↦ g (js i) i)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) = _
    calc
      _ = PiTensorProduct.map (fun i ↦ (g (js i) i).comp (G.blockProj i 0)) T.t :=
        (LinearMap.congr_fun (PiTensorProduct.map_comp
          (f := fun i ↦ G.blockProj i 0) (g := fun i ↦ g (js i) i)) T.t).symm
      _ = _ := by simp only [hcomp]
  apply mme_tensor_family_direct_sum_restrict_of_mixed_maps P B g
  · intro j
    exact hmap (fun _ ↦ j)
  · intro js hnonconstant
    rw [hmap, ← (Basis.piTensorProduct b).sum_repr T.t, map_sum]
    apply Finset.sum_eq_zero
    intro x _
    rw [map_smul]
    by_cases hc : (Basis.piTensorProduct b).repr T.t x = 0
    · rw [hc, zero_smul]
    · have hr : ∃ i, ¬ keep (js i) i (x i) := by
        by_contra h
        have hk : ∀ i, keep (js i) i (x i) := fun i ↦ by
          by_contra hi
          exact h ⟨i, hi⟩
        obtain ⟨j, hj⟩ := hunique x js hc hk
        exact hnonconstant j hj
      obtain ⟨i, hi⟩ := hr
      have hz : f (js i) i (b i (x i)) = 0 :=
        rejected_projection T b (keep (js i)) i (x i) hi
      rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod,
        (PiTensorProduct.tprod K).map_coord_zero i hz, smul_zero]
