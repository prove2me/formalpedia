-- Prove2me | solution 1 for mme_primary_hash_family_sharedZ_star_grading_components
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:11:00.561515+00:00
-- url     : https://prove2.me/submissions/778b75e6-44a0-4bb6-99cd-2859d8868a2e

import Definitions.Def_mme_coupled_Ctensor_packaging_data

open MME PiTensorProduct BigOperators Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace CoupledCTensorPackaging

variable {K : Type u} [Field K]
variable {T : TensorObj K 3} (grading : T.TypeGrading 3)
variable {N L G A H : ℕ}

theorem sharedZ_basisGrade_mem_of_const
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ]
    (b : Basis ι K V) (a : κ) (x : V) :
    x ∈ cwBasisGrade b (fun _ => a) a := by
  classical
  rw [← b.sum_repr x]
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, by simp, rfl⟩

theorem componentInclusion_mem
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3)
    (x : (componentObj grading family a h).V i) :
    componentInclusion grading family a h i x ∈
      (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) := by
  classical
  fin_cases i
  · letI : Module K
        (∀ k : Fin H, (componentObj grading family a k).V 0) :=
      Pi.module _ _ _
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h) x ∈ _
    rw [← (Module.finBasis K
      ((componentObj grading family a h).V 0)).sum_repr x]
    rw [map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h)
        ((Module.finBasis K
          ((componentObj grading family a h).V 0)) j) ∈
      cwBasisGrade (starBasis grading family a 0)
        (starBasisGrade grading family a 0) (Fin.castSucc h)
    unfold cwBasisGrade
    apply Submodule.subset_span
    refine ⟨⟨h, j⟩, ?_, ?_⟩
    · simp [starBasisGrade, cTensorOneHOneAddress]
    · change (Pi.basis (fun k : Fin H =>
          Module.finBasis K ((componentObj grading family a k).V 0))
        ⟨h, j⟩) = _
      rw [Pi.basis_apply, LinearMap.single_apply]
  · letI : Module K
        (∀ k : Fin H, (componentObj grading family a k).V 1) :=
      Pi.module _ _ _
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h) x ∈ _
    rw [← (Module.finBasis K
      ((componentObj grading family a h).V 1)).sum_repr x]
    rw [map_sum]
    simp only [map_smul]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    change (LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h)
        ((Module.finBasis K
          ((componentObj grading family a h).V 1)) j) ∈
      cwBasisGrade (starBasis grading family a 1)
        (starBasisGrade grading family a 1) (Fin.castSucc h)
    unfold cwBasisGrade
    apply Submodule.subset_span
    refine ⟨⟨h, j⟩, ?_, ?_⟩
    · simp [starBasisGrade, cTensorOneHOneAddress]
    · change (Pi.basis (fun k : Fin H =>
          Module.finBasis K ((componentObj grading family a k).V 1))
        ⟨h, j⟩) = _
      rw [Pi.basis_apply, LinearMap.single_apply]
  · change (componentZEquiv grading family a h) x ∈
      cwBasisGrade (starBasis grading family a 2)
        (starBasisGrade grading family a 2) (Fin.last H)
    simpa only [starGrading, starBasisGrade,
      cTensorOneHOneAddress] using
      sharedZ_basisGrade_mem_of_const
        (starBasis grading family a 2) (Fin.last H)
        ((componentZEquiv grading family a h) x)

noncomputable def componentLift
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (componentObj grading family a h).V i →ₗ[K]
      (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) :=
  fun i => LinearMap.codRestrict _
    (componentInclusion grading family a h i)
    (componentInclusion_mem grading family a h i)

theorem blockProj_component_same
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3)
    (x : (componentObj grading family a h).V i) :
    (starGrading grading family a).blockProj i
        (cTensorOneHOneAddress H h i)
        (componentInclusion grading family a h i x) =
      componentLift grading family a h i x := by
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _
    (componentInclusion_mem grading family a h i x)]
  apply Subtype.ext
  rfl

theorem blockProj_component_ne_zero_mode0
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h k : Fin H) (hhk : h ≠ k) :
    ((starGrading grading family a).blockProj 0
        (cTensorOneHOneAddress H h 0)).comp
        (componentInclusion grading family a k 0) = 0 := by
  apply LinearMap.ext
  intro x
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (starGrading grading family a) 0
    (cTensorOneHOneAddress H h 0)
    (cTensorOneHOneAddress H k 0)
    (by
      intro heq
      apply hhk
      exact Fin.castSucc_injective H heq)
    (componentInclusion grading family a k 0 x)
    (componentInclusion_mem grading family a k 0 x)

theorem sharedZ_piTensorMap_eq_zero_of_coord
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, V i →ₗ[K] W i) (i : Fin 3) (hi : f i = 0)
    (x : PiTensorProduct K V) :
    PiTensorProduct.map f x = 0 := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      rw [map_smul, PiTensorProduct.map_tprod]
      suffices tprod K (fun j => f j (v j)) = 0 by simp [this]
      apply (PiTensorProduct.tprod K).map_coord_zero i
      rw [hi]
      rfl
  | add x y ihx ihy => simp [ihx, ihy]

theorem projected_component_eq_zero_of_ne
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h k : Fin H) (hhk : h ≠ k) :
    PiTensorProduct.map
        (fun i => ((starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i)).comp
            (componentInclusion grading family a k i))
        (componentObj grading family a k).t = 0 := by
  apply sharedZ_piTensorMap_eq_zero_of_coord _ 0
  exact blockProj_component_ne_zero_mode0 grading family a h k hhk

theorem star_blockTensor_eq_component
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    (starGrading grading family a).blockTensor
        (cTensorOneHOneAddress H h) =
      PiTensorProduct.map (componentLift grading family a h)
        (componentObj grading family a h).t := by
  classical
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun i => (starGrading grading family a).blockProj i
        (cTensorOneHOneAddress H h i))
      (∑ k : Fin H,
        PiTensorProduct.map (componentInclusion grading family a k)
          (componentObj grading family a k).t) = _
  rw [map_sum]
  rw [Finset.sum_eq_single h]
  · change ((PiTensorProduct.map
        (fun i => (starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i))).comp
        (PiTensorProduct.map (componentInclusion grading family a h)))
          (componentObj grading family a h).t = _
    rw [← PiTensorProduct.map_comp]
    have hmaps :
        (fun i => ((starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i)).comp
            (componentInclusion grading family a h i)) =
          componentLift grading family a h := by
      funext i
      apply LinearMap.ext
      intro x
      exact blockProj_component_same grading family a h i x
    rw [hmaps]
  · intro k _ hkh
    change ((PiTensorProduct.map
        (fun i => (starGrading grading family a).blockProj i
          (cTensorOneHOneAddress H h i))).comp
        (PiTensorProduct.map (componentInclusion grading family a k)))
          (componentObj grading family a k).t = 0
    rw [← PiTensorProduct.map_comp]
    exact projected_component_eq_zero_of_ne grading family a h k hkh.symm
  · exact fun hh => (hh (Finset.mem_univ h)).elim

noncomputable def componentDrop
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) : ∀ i : Fin 3,
    (starGrading grading family a).classOf i
        (cTensorOneHOneAddress H h i) →ₗ[K]
      (componentObj grading family a h).V i
  | 0 => (LinearMap.proj (R := K)
      (φ := fun k : Fin H => (componentObj grading family a k).V 0) h).comp
      ((starGrading grading family a).classOf 0
        (cTensorOneHOneAddress H h 0)).subtype
  | 1 => (LinearMap.proj (R := K)
      (φ := fun k : Fin H => (componentObj grading family a k).V 1) h).comp
      ((starGrading grading family a).classOf 1
        (cTensorOneHOneAddress H h 1)).subtype
  | 2 => (componentZEquiv grading family a h).symm.toLinearMap.comp
      ((starGrading grading family a).classOf 2
        (cTensorOneHOneAddress H h 2)).subtype

theorem componentDrop_comp_lift
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) (i : Fin 3) :
    (componentDrop grading family a h i).comp
        (componentLift grading family a h i) =
      LinearMap.id := by
  apply LinearMap.ext
  intro x
  fin_cases i
  · change ((LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 0) h) x) h = x
    rw [LinearMap.single_apply]
    simp
  · change ((LinearMap.single K
      (fun k : Fin H => (componentObj grading family a k).V 1) h) x) h = x
    rw [LinearMap.single_apply]
    simp
  · simp only [componentDrop, componentLift, LinearMap.comp_apply,
      componentInclusion, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.id_apply]
    exact (componentZEquiv grading family a h).symm_apply_apply x

theorem component_block_isomorphic
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (h : Fin H) :
    TensorObj.Isomorphic
      (componentObj grading family a h)
      ((starGrading grading family a).blockSubtensor
        (cTensorOneHOneAddress H h)) := by
  constructor
  · refine ⟨componentDrop grading family a h, ?_⟩
    change PiTensorProduct.map (componentDrop grading family a h)
      ((starGrading grading family a).blockTensor
        (cTensorOneHOneAddress H h)) = _
    rw [star_blockTensor_eq_component grading family a h]
    change PiTensorProduct.map (componentDrop grading family a h)
        (PiTensorProduct.map (componentLift grading family a h)
          (componentObj grading family a h).t) = _
    change ((PiTensorProduct.map (componentDrop grading family a h)).comp
      (PiTensorProduct.map (componentLift grading family a h)))
        (componentObj grading family a h).t = _
    rw [← PiTensorProduct.map_comp]
    have hmaps :
        (fun i => (componentDrop grading family a h i).comp
          (componentLift grading family a h i)) =
          fun _ => LinearMap.id := by
      funext i
      exact componentDrop_comp_lift grading family a h i
    rw [hmaps, PiTensorProduct.map_id]
    rfl
  · refine ⟨componentLift grading family a h, ?_⟩
    exact (star_blockTensor_eq_component grading family a h).symm

theorem sharedZ_starGrading_supported
    (family : CWQ6PrimaryHashFamily N L G A H)
    (a : Fin A) (sigma : Fin 3 → Fin (H + 1))
    (hsigma : sigma ∉ Finset.univ.image (cTensorOneHOneAddress H)) :
    (starGrading grading family a).blockTensor sigma = 0 := by
  classical
  unfold TensorObj.TypeGrading.blockTensor
  change PiTensorProduct.map
      (fun i => (starGrading grading family a).blockProj i (sigma i))
      (∑ k : Fin H,
        PiTensorProduct.map (componentInclusion grading family a k)
          (componentObj grading family a k).t) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro k _
  have hne : ∃ i : Fin 3,
      sigma i ≠ cTensorOneHOneAddress H k i := by
    by_contra h
    push_neg at h
    apply hsigma
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_univ k, ?_⟩
    funext i
    exact (h i).symm
  obtain ⟨i, hi⟩ := hne
  change ((PiTensorProduct.map
      (fun j => (starGrading grading family a).blockProj j (sigma j))).comp
      (PiTensorProduct.map (componentInclusion grading family a k)))
        (componentObj grading family a k).t = 0
  rw [← PiTensorProduct.map_comp]
  apply sharedZ_piTensorMap_eq_zero_of_coord _ i
  apply LinearMap.ext
  intro x
  exact TensorObj.TypeGrading.blockProj_apply_mem_ne
    (starGrading grading family a) i
    (sigma i) (cTensorOneHOneAddress H k i) hi
    (componentInclusion grading family a k i x)
    (componentInclusion_mem grading family a k i x)


end CoupledCTensorPackaging

open CoupledCTensorPackaging

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} (grading : T.TypeGrading 3)
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H) :
    ∀ a : Fin A,
      (∀ σ : Fin 3 → Fin (H + 1),
        σ ∉ Finset.univ.image (cTensorOneHOneAddress H) →
          (starGrading grading family a).blockTensor σ = 0) ∧
      ∀ h : Fin H,
        TensorObj.Isomorphic
          (componentObj grading family a h)
          ((starGrading grading family a).blockSubtensor
            (cTensorOneHOneAddress H h)) := by
  intro a
  exact ⟨sharedZ_starGrading_supported grading family a,
    component_block_isomorphic grading family a⟩
