-- Prove2me | solution 1 for mme_profiled_CW_joint_projection_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T00:55:20.790992+00:00
-- url     : https://prove2.me/submissions/85070bce-224f-4cb8-a755-2d55b649d9c4

import Definitions.Def_mme_recursive_regional_CW_data
import Theorems.Thm_mme_recursive_regional_CW_plan_sound
import Theorems.Thm_mme_profiled_CW_region_product_restrict
import Theorems.Thm_mme_regional_copied_restrictions_product
import Theorems.Thm_mme_profiled_CW_mode_permutation_iso
import Theorems.Thm_mme_MMObj_permObj_swapFirstTwo
import Theorems.Thm_mme_recursive_profiled_CW_exact_step
import Theorems.Thm_mme_basis_projected_type_cover_restrict
import Theorems.Thm_mme_type_cover_uniform_copy_extraction
import Theorems.Thm_mme_batched_restrictions_compose
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_toQ_kronFin
import Theorems.Thm_mme_CW_three_canonical_support
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_dwz_cw_square_fine_split_grading
import Definitions.Def_mme_complete_split_profile_projection
import Mathlib.Algebra.BigOperators.Fin

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.DWZStep1Support MME.CompleteSplit Module PiTensorProduct TensorProduct
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

universe u

private theorem kronFinFamilyModeMap_comp {K : Type u} [Field K] {d : ℕ} :
    ∀ (n : ℕ) (X Y Z : Fin n → TensorObj K d)
      (f : ∀ r i, (X r).V i →ₗ[K] (Y r).V i) (g : ∀ r i, (Y r).V i →ₗ[K] (Z r).V i)
      (i : Fin d),
      (kronFinFamilyModeMap n Y Z g i).comp (kronFinFamilyModeMap n X Y f i) =
        kronFinFamilyModeMap n X Z (fun r j ↦ (g r j).comp (f r j)) i
  | 0, _, _, _, _, _, _ => LinearMap.id_comp _
  | n + 1, X, Y, Z, f, g, i => by
      change (TensorProduct.map (g 0 i) (kronFinFamilyModeMap n (fun r : Fin n ↦ Y r.succ)
          (fun r : Fin n ↦ Z r.succ) (fun r j ↦ g r.succ j) i)).comp
        (TensorProduct.map (f 0 i) (kronFinFamilyModeMap n (fun r : Fin n ↦ X r.succ)
          (fun r : Fin n ↦ Y r.succ) (fun r j ↦ f r.succ j) i)) =
        TensorProduct.map ((g 0 i).comp (f 0 i)) (kronFinFamilyModeMap n (fun r : Fin n ↦ X r.succ)
          (fun r : Fin n ↦ Z r.succ) (fun r j ↦ (g r.succ j).comp (f r.succ j)) i)
      rw [← TensorProduct.map_comp, kronFinFamilyModeMap_comp n]

private theorem kronFinModePiBasis_succ_apply' {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 1) → TensorObj K d) (i : Fin d)
    {index : Fin (n + 1) → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (w : ∀ r, index r) :
    kronFinModePiBasis (n + 1) T i b w =
      (b 0 (w 0)) ⊗ₜ[K]
        (kronFinModePiBasis n (fun r : Fin n ↦ T r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ w r.succ)) := by
  change (((b 0).tensorProduct
    (kronFinModePiBasis n (fun r : Fin n ↦ T r.succ) i
      (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) w = _
  rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
    Module.Basis.tensorProduct_apply]
  rfl

/-- Pointwise version of `kronFinFamilyModeMap_basis`: only the selected word is needed. -/
private theorem kronFinFamilyModeMap_basis_at {K : Type u} [Field K] {d n : ℕ}
    (X Y : Fin n → TensorObj K d) (i : Fin d)
    {indexX indexY : Fin n → Type u}
    (bX : ∀ r, Basis (indexX r) K ((X r).V i))
    (bY : ∀ r, Basis (indexY r) K ((Y r).V i))
    (f : ∀ r j, (X r).V j →ₗ[K] (Y r).V j)
    (w : ∀ r, indexX r) (v : ∀ r, indexY r)
    (hf : ∀ r, f r i (bX r (w r)) = bY r (v r)) :
    kronFinFamilyModeMap n X Y f i (kronFinModePiBasis n X i bX w) =
      kronFinModePiBasis n Y i bY v := by
  induction n with
  | zero =>
      letI : Unique (∀ r : Fin 0, indexX r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      letI : Unique (∀ r : Fin 0, indexY r) :=
        { default := fun r ↦ r.elim0
          uniq := fun _ ↦ by funext r; exact r.elim0 }
      simp only [kronFinFamilyModeMap, kronFinModePiBasis]
      calc
        _ = (1 : K) := by
          exact Module.Basis.singleton_apply _ K w
        _ = _ := by
          symm
          exact Module.Basis.singleton_apply _ K _
  | succ n ih =>
      rw [kronFinModePiBasis_succ_apply', kronFinModePiBasis_succ_apply']
      change TensorProduct.map (f 0 i)
          (kronFinFamilyModeMap n (fun r : Fin n ↦ X r.succ) (fun r : Fin n ↦ Y r.succ)
            (fun r j ↦ f r.succ j) i)
          ((bX 0 (w 0)) ⊗ₜ[K] kronFinModePiBasis n (fun r : Fin n ↦ X r.succ) i
            (fun r ↦ bX r.succ) (fun r ↦ w r.succ)) = _
      rw [TensorProduct.map_tmul, hf 0]
      rw [ih (fun r : Fin n ↦ X r.succ) (fun r : Fin n ↦ Y r.succ)
        (fun r ↦ bX r.succ) (fun r ↦ bY r.succ) (fun r j ↦ f r.succ j)
        (fun r ↦ w r.succ) (fun r ↦ v r.succ) (fun r ↦ hf r.succ)]

/-- The joint projection onto a predicate that implies every part predicate is a
restriction of the Kronecker product of the part projections. Converse direction of
`mme_profiled_CW_region_product_restrict`. -/
theorem solution {K : Type u} [Field K] {N parts : ℕ}
    (size : Fin parts → ℕ) (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin N)
    (T : ∀ j, Predicate (size j)) (Q : Predicate N)
    (hQ : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j,r⟩))) :
    TensorObj.Restrict (tensor K Q) (kronFin parts (fun j ↦ tensor K (T j))) := by
  classical
  let R := fun j ↦ raw K (size j)
  let S := fun j ↦ tensor K (T j)
  let G := fun j ↦ (R j).basisAllAllowedGrading (canonical K (size j))
    (fun i x ↦ T j i (fine x))
  let proj : ∀ j i, (R j).V i →ₗ[K] (S j).V i := fun j i ↦ (G j).blockProj i 0
  let incl : ∀ j i, (S j).V i →ₗ[K] (R j).V i := fun j i ↦ ((G j).classOf i 0).subtype
  let GQ := (raw K N).basisAllAllowedGrading (canonical K N) (fun i x ↦ Q i (fine x))
  obtain ⟨phi, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K 5) (fun i ↦ (MME.DWZStep1Support.cwThreeCanonicalBasis K 5 i).reindex Equiv.ulift.symm)
    size positions.symm
  change PiTensorProduct.map (fun i ↦ (phi i).toLinearMap) (raw K N).t =
    (kronFin parts R).t at ht
  have hB (i : Fin 3) (x : Coordinate.{u} N) :
      phi i (canonical K N i x) =
        kronFinModePiBasis parts R i (fun j ↦ canonical K (size j) i)
          (fun j r ↦ x (positions ⟨j,r⟩)) := hb i x
  let h : ∀ i, (kronFin parts S).V i →ₗ[K] (tensor K Q).V i := fun i ↦
    (GQ.blockProj i 0).comp ((phi i).symm.toLinearMap.comp (kronFinFamilyModeMap parts S R incl i))
  have hS : PiTensorProduct.map (kronFinFamilyModeMap parts R S proj) (kronFin parts R).t =
      (kronFin parts S).t :=
    kronFinFamilyModeMap_preserves_tensor R S proj (fun _ ↦ rfl)
  have key : ∀ i, ((h i).comp (kronFinFamilyModeMap parts R S proj i)).comp (phi i).toLinearMap =
      GQ.blockProj i 0 := by
    intro i
    apply (canonical K N i).ext
    intro x
    have hcomp := kronFinFamilyModeMap_comp parts R S R proj incl i
    change GQ.blockProj i 0 ((phi i).symm
      (((kronFinFamilyModeMap parts S R incl i).comp (kronFinFamilyModeMap parts R S proj i))
        (phi i (canonical K N i x)))) = GQ.blockProj i 0 (canonical K N i x)
    rw [hcomp, hB]
    by_cases hall : ∀ j, T j i (fine (fun r ↦ x (positions ⟨j,r⟩)))
    · rw [kronFinFamilyModeMap_basis_at R R i (fun j ↦ canonical K (size j) i)
        (fun j ↦ canonical K (size j) i) (fun r j ↦ (incl r j).comp (proj r j))
        (fun j r ↦ x (positions ⟨j,r⟩)) (fun j r ↦ x (positions ⟨j,r⟩)) ?_]
      · rw [← hB, LinearEquiv.symm_apply_apply]
      · intro j
        change (((G j).blockProj i 0 (canonical K (size j) i (fun r ↦ x (positions ⟨j,r⟩)))) :
          (R j).V i) = _
        rw [TensorObj.TypeGrading.blockProj_apply_mem (G j) i 0 _
          (Submodule.subset_span ⟨_, if_pos (hall j), rfl⟩)]
    · obtain ⟨j, hj⟩ := not_forall.mp hall
      rw [kronFinFamilyModeMap_basis_eq_zero_of_exists R R i (fun j ↦ canonical K (size j) i)
        (fun r j ↦ (incl r j).comp (proj r j)) (fun j r ↦ x (positions ⟨j,r⟩)) ⟨j, ?_⟩]
      · have hnQ : ¬ Q i (fine x) := fun hq ↦ hj (hQ i (fine x) hq j)
        rw [map_zero, map_zero, TensorObj.TypeGrading.blockProj_apply_mem_ne GQ i 0 1 (by decide) _
          (Submodule.subset_span ⟨x, if_neg hnQ, rfl⟩)]
      · change (((G j).blockProj i 0 (canonical K (size j) i (fun r ↦ x (positions ⟨j,r⟩)))) :
          (R j).V i) = 0
        rw [TensorObj.TypeGrading.blockProj_apply_mem_ne (G j) i 0 1 (by decide) _
          (Submodule.subset_span ⟨_, if_neg hj, rfl⟩)]
        rfl
  refine ⟨h, ?_⟩
  have hfun : (fun i ↦ ((h i).comp (kronFinFamilyModeMap parts R S proj i)).comp
      (phi i).toLinearMap) = fun i ↦ GQ.blockProj i 0 := funext key
  calc PiTensorProduct.map h (kronFin parts S).t
      = PiTensorProduct.map h (PiTensorProduct.map (kronFinFamilyModeMap parts R S proj)
          (PiTensorProduct.map (fun i ↦ (phi i).toLinearMap) (raw K N).t)) := by rw [ht, hS]
    _ = PiTensorProduct.map (fun i ↦ ((h i).comp (kronFinFamilyModeMap parts R S proj i)).comp
          (phi i).toLinearMap) (raw K N).t := by
        simp only [PiTensorProduct.map_comp, LinearMap.comp_apply]
        rfl
    _ = PiTensorProduct.map (fun i ↦ GQ.blockProj i 0) (raw K N).t := by rw [hfun]; rfl
    _ = (tensor K Q).t := rfl
