-- Prove2me | solution 1 for mme_basis_projected_mode_permutation_iso
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T15:13:24.3107+00:00
-- url     : https://prove2.me/submissions/e011a32f-49e8-49aa-9dd1-2afa8385e0ad

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_permutation
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

open MME MME.TensorObj Module PiTensorProduct BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
universe u

private theorem allowed_class_span
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : ∀ i, I i → Prop) (i : Fin 3) :
    (T.basisAllAllowedGrading b allowed).classOf i 0 =
      Submodule.span K (b i '' {w | allowed i w}) := by
  classical
  change Submodule.span K
    (b i '' {w | (if allowed i w then (0 : Fin 2) else 1) = 0}) = _
  have hs : {w | (if allowed i w then (0 : Fin 2) else 1) = 0} =
      {w | allowed i w} := by
    ext w
    simp
  rw [hs]

private theorem reject {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Type u} (b : ∀ i, Basis I K (T.V i)) (P : Fin 3 → I → Prop)
    (i : Fin 3) (x : I) (hx : ¬ P i x) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i x) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne
    (T.basisAllAllowedGrading b P) i 0 1 (by decide)
  exact Submodule.subset_span ⟨x, by simp [hx], rfl⟩

theorem solution {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Type u} [Fintype I] (b : ∀ i, Basis I K (T.V i))
    (sigma : Equiv.Perm (Fin 3)) (P : Fin 3 → I → Prop)
    (hsymmetric : ∀ x : Fin 3 → I,
      (Basis.piTensorProduct b).repr T.t (fun i ↦ x (sigma i)) =
        (Basis.piTensorProduct b).repr T.t x) :
    Isomorphic (T.basisAllAllowedSubtensor b (fun i ↦ P (sigma.symm i)))
      (permObj sigma (T.basisAllAllowedSubtensor b P)) := by
  classical
  let E := fun i ↦ (b (sigma.symm i)).equiv (b i) (Equiv.refl I)
  have hE (i) (v : T.V (sigma.symm i)) (x : I) :
      (b i).repr (E i v) x = (b (sigma.symm i)).repr v x := by
    have he : ((b i).coord x).comp (E i).toLinearMap = (b (sigma.symm i)).coord x := by
      apply (b (sigma.symm i)).ext
      intro y
      simp [E, Basis.equiv_apply, Basis.coord_apply]
    exact LinearMap.congr_fun he v
  have hrepr (v : PiTensorProduct K T.V) (x : Fin 3 → I) :
      (Basis.piTensorProduct b).repr
        (PiTensorProduct.map (fun i ↦ (E i).toLinearMap)
          (PiTensorProduct.reindex K T.V sigma v)) x =
        (Basis.piTensorProduct b).repr v (fun i ↦ x (sigma i)) := by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.reindex_tprod, PiTensorProduct.map_tprod,
        Finsupp.smul_apply, Basis.piTensorProduct_repr_tprod_apply]
      congr 1
      calc
        _ = ∏ i, (b (sigma.symm i)).repr (v (sigma.symm i)) (x i) :=
          Finset.prod_congr rfl (fun i _ ↦ hE i (v (sigma.symm i)) (x i))
        _ = _ := by
          simpa only [Equiv.apply_symm_apply] using
            sigma.symm.prod_comp (fun i ↦ (b i).repr (v i) (x (sigma i)))
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  have hraw : PiTensorProduct.map (fun i ↦ (E i).toLinearMap)
      (PiTensorProduct.reindex K T.V sigma T.t) = T.t := by
    apply (Basis.piTensorProduct b).repr.injective
    ext x
    exact (hrepr T.t x).trans (hsymmetric x)
  let G := T.basisAllAllowedGrading b P
  let Q := T.basisAllAllowedGrading b (fun i ↦ P (sigma.symm i))
  have hspace (i) : Submodule.map (E i).toLinearMap (G.classOf (sigma.symm i) 0) =
      Q.classOf i 0 := by
    have hs := allowed_class_span T b P (sigma.symm i)
    have hq := allowed_class_span T b (fun i ↦ P (sigma.symm i)) i
    change Submodule.map (E i).toLinearMap (G.classOf (sigma.symm i) 0) = Q.classOf i 0
    rw [hs, hq, Submodule.map_span]
    congr 1
    ext v
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, (Basis.equiv_apply (b (sigma.symm i)) x (b i) (Equiv.refl I)).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨b (sigma.symm i) x, ⟨x, hx, rfl⟩,
        Basis.equiv_apply (b (sigma.symm i)) x (b i) (Equiv.refl I)⟩
  let F : ∀ i, G.classOf (sigma.symm i) 0 ≃ₗ[K] Q.classOf i 0 :=
    fun i ↦ (E i).ofSubmodules _ _ (hspace i)
  have hF (i) : (F i).toLinearMap.comp (G.blockProj (sigma.symm i) 0) =
      (Q.blockProj i 0).comp (E i).toLinearMap := by
    apply (b (sigma.symm i)).ext
    intro x
    change F i (G.blockProj (sigma.symm i) 0 (b (sigma.symm i) x)) =
      Q.blockProj i 0 (E i (b (sigma.symm i) x))
    by_cases hx : P (sigma.symm i) x
    · have hm : b (sigma.symm i) x ∈ G.classOf (sigma.symm i) 0 :=
        Submodule.subset_span ⟨x, by simp [hx], rfl⟩
      have hm' : b i x ∈ Q.classOf i 0 :=
        Submodule.subset_span ⟨x, by simp [hx], rfl⟩
      have he : E i (b (sigma.symm i) x) = b i x :=
        Basis.equiv_apply (b (sigma.symm i)) x (b i) (Equiv.refl I)
      rw [he, TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm,
        TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm']
      apply Subtype.ext
      exact he
    · rw [reject T b P (sigma.symm i) x hx, map_zero]
      change 0 = Q.blockProj i 0 (E i (b (sigma.symm i) x))
      rw [Basis.equiv_apply]
      exact (reject T b (fun i ↦ P (sigma.symm i)) i x hx).symm
  have hcomm (v : PiTensorProduct K T.V) :
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap) (PiTensorProduct.reindex K
        (fun i ↦ G.classOf i 0) sigma (PiTensorProduct.map (fun i ↦ G.blockProj i 0) v)) =
      PiTensorProduct.map (fun i ↦ Q.blockProj i 0)
        (PiTensorProduct.map (fun i ↦ (E i).toLinearMap)
          (PiTensorProduct.reindex K T.V sigma v)) := by
    induction v using PiTensorProduct.induction_on with
    | smul_tprod a v =>
      simp only [map_smul, PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]
      congr 1
      congr 1
      funext i
      exact LinearMap.congr_fun (hF i) (v (sigma.symm i))
    | add x y hx hy => simp only [map_add, hx, hy]
  have hresult : PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (permObj sigma (T.basisAllAllowedSubtensor b P)).t =
      (T.basisAllAllowedSubtensor b (fun i ↦ P (sigma.symm i))).t :=
    (hcomm T.t).trans (congrArg (PiTensorProduct.map (fun i ↦ Q.blockProj i 0)) hraw)
  refine ⟨⟨fun i ↦ (F i).toLinearMap, hresult⟩, ⟨fun i ↦ (F i).symm.toLinearMap, ?_⟩⟩
  change (PiTensorProduct.congr F).symm _ = _
  exact (LinearEquiv.symm_apply_eq (PiTensorProduct.congr F)).2 hresult.symm
