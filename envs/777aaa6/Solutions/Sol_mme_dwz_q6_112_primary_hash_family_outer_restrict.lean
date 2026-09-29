-- Prove2me | solution 1 for mme_dwz_q6_112_primary_hash_family_outer_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:38:06.334447+00:00
-- url     : https://prove2.me/submissions/b1cb0407-5d75-4d3d-911f-a542299ee83f

import Theorems.Thm_mme_dwz_q6_canonical_112_source_router_Z_basis
import Theorems.Thm_mme_dwz_q6_112_router_projector_descent_poly
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support
import Theorems.Thm_mme_primary_hash_family_sharedZ_outer_extraction_exact
import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.DWZComponentRestriction PiTensorProduct Module
open BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 2048

namespace MME.DWZComponentRestriction

private noncomputable def gradedAddressBlockLengthEquivPublic
    {K : Type u} [Field K] {T : TensorObj K 3} {t R S : ℕ}
    (G : T.TypeGrading t) (h : R = S)
    (a : Fin 3 → Fin R → Fin t) (i : Fin 3) :
    (gradedAddressBlock G a).V i ≃ₗ[K]
      (gradedAddressBlock G
        (fun j r ↦ a j (Fin.cast h.symm r))).V i := by
  subst S
  exact LinearEquiv.refl K _

private noncomputable def kronPowLengthEquivPublic
    {K : Type u} [Field K] {d R S : ℕ} (T : TensorObj K d)
    (h : R = S) (i : Fin d) :
    (T.kronPow R).V i ≃ₗ[K] (T.kronPow S).V i := by
  subst S
  exact LinearEquiv.refl K _

private theorem kronPowLengthEquivPublic_symm_maps_tensor
    {K : Type u} [Field K] {d R S : ℕ} (T : TensorObj K d)
    (h : R = S) :
    PiTensorProduct.map
        (fun i ↦ (kronPowLengthEquivPublic T h i).symm.toLinearMap)
        (T.kronPow S).t = (T.kronPow R).t := by
  subst S
  change PiTensorProduct.map (fun _ ↦ LinearMap.id) (T.kronPow R).t = _
  rw [PiTensorProduct.map_id]
  rfl

private theorem gradedAddressProj_lengthEquivPublic_symm_comp
    {K : Type u} [Field K] {T : TensorObj K 3} {t R S : ℕ}
    (G : T.TypeGrading t) (h : R = S)
    (a : Fin 3 → Fin R → Fin t) (i : Fin 3) :
    (gradedAddressBlockLengthEquivPublic G h a i).symm.toLinearMap.comp
        (gradedAddressProj G S
          (fun j r ↦ a j (Fin.cast h.symm r)) i) =
      (gradedAddressProj G R a i).comp
        (kronPowLengthEquivPublic T h i).symm.toLinearMap := by
  subst S
  rfl

private theorem kronPowModeMap_maps_tensor_public
    {K : Type u} [Field K] {d : ℕ} {T S : TensorObj K d}
    (f : ∀ i : Fin d, T.V i →ₗ[K] S.V i)
    (hf : PiTensorProduct.map f T.t = S.t) : ∀ n : ℕ,
    PiTensorProduct.map (fun i ↦ kronPowModeMap i (f i) n)
        (T.kronPow n).t = (S.kronPow n).t
  | 0 => by
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (TensorObj.oneObj (K := K) (d := d)).t =
        (TensorObj.oneObj (K := K) (d := d)).t
      rw [PiTensorProduct.map_id]
      rfl
  | n + 1 => by
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (f i)
            (kronPowModeMap i (f i) n))
          (interchange T.t (T.kronPow n).t) =
        interchange S.t (S.kronPow n).t
      rw [TensorObj.TypeGrading.kronMap_interchange, hf]
      rw [kronPowModeMap_maps_tensor_public f hf n]

/-- The shared-Z extraction attached to an exact primary family descends to
the literal prescribed-profile enhanced row-112 power. -/
theorem outerRestrictProof
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (CoupledCTensorPackaging.starObj
          (dwzQ6CoupledGrading K) family))
      (restrictedComponentPower K (12 : Fin 15) m) := by
  let G0 := dwzQ6CoupledGrading K
  let n := MME.DWZTable2Counts.component (12 : Fin 15) * m
  have hn : n = 2 * (50000000 * (20088623 * m)) := by
    change 2008862300000000 * m =
      2 * (50000000 * (20088623 * m))
    ring
  obtain ⟨router, hrouterTensor, hrouterZ⟩ :=
    mme_dwz_q6_canonical_112_source_router_Z_basis K
  let exactAddress (a : Fin A) :=
    CoupledCTensorPackaging.componentExactAddress family a
      (CoupledCTensorPackaging.firstFiberIndex family)
  let address : Fin A → Fin 3 → Fin n → Fin 3 :=
    fun a i r ↦ (exactAddress a).1 i (Fin.cast (hn.symm).symm r)
  let post : ∀ a : Fin A,
      (gradedAddressBlock G0 (address a)).V 2 →ₗ[K]
        (TensorObj.bigAdd
          (CoupledCTensorPackaging.starObj G0 family)).V 2 := fun a ↦
    (gradedBigAddSlot A
      (CoupledCTensorPackaging.starObj G0 family) a 2).comp
        (gradedAddressBlockLengthEquivPublic G0 hn.symm
          (exactAddress a).1 2).symm.toLinearMap
  let extract : ∀ i : Fin 3,
      ((coupledObj K 6).kronPow n).V i →ₗ[K]
        (TensorObj.bigAdd
          (CoupledCTensorPackaging.starObj G0 family)).V i := fun i ↦
    (CoupledCTensorPackaging.outerExtractionMap G0 family i).comp
      (kronPowLengthEquivPublic (coupledObj K 6) hn.symm i).symm.toLinearMap
  let cZ : Basis (ULift.{u} (DWZCanonical112Coord 6 (2 : Fin 3))) K
      ((coupledObj K 6).V 2) :=
    (dwzQ6CoupledBasis K 2).reindex Equiv.ulift.symm
  let targetGrade :
      ULift.{u} (DWZCanonical112Coord 6 (2 : Fin 3)) → Fin 3 :=
    fun j ↦ dwzQ6CoupledCoordGrade 2 j.down
  let label : LiftedCoarsePair.{u} 6 2 →
      ULift.{u} (DWZCanonical112Coord 6 (2 : Fin 3)) :=
    fun p ↦ ULift.up (dwzQ6Canonical112ZCoord p)
  have hrouterZ' : ∀ p : LiftedCoarsePair.{u} 6 2,
      router 2 (canonicalComponentZBasis K 12 p) =
        cZ (label p) := by
    intro p
    rw [show cZ (label p) =
        dwzQ6CoupledBasis K 2 (dwzQ6Canonical112ZCoord p) by
      exact Module.Basis.reindex_apply
        (dwzQ6CoupledBasis K 2) Equiv.ulift.symm (label p)]
    exact hrouterZ p
  have htranslate : ∀ p : LiftedCoarsePair.{u} 6 2,
      p.leftGrade =
        mme_dwz_q6_coupled_Z_leftGrade
          (targetGrade (label p)) := by
    intro p
    exact (mme_dwz_q6_112_Z_decoder_pair_and_leftGrade p).2
  have haddress : ∀ (a : Fin A)
      (hlen : MME.DWZTable2Counts.component (12 : Fin 15) * m =
        2 * (50000000 * (20088623 * m))) (i) (r),
      address a i r = (exactAddress a).1 i (Fin.cast hlen r) := by
    intro a hlen i r
    exact congrArg
      (fun hproof : n = 2 * (50000000 * (20088623 * m)) ↦
        (exactAddress a).1 i (Fin.cast hproof r))
      (Subsingleton.elim _ _)
  have hGzero : ∀ (a : Fin 3)
      (j : ULift.{u} (DWZCanonical112Coord 6 (2 : Fin 3))),
      targetGrade j ≠ a → G0.blockProj 2 a (cZ j) = 0 := by
    intro a j hne
    rw [show cZ j = dwzQ6CoupledBasis K 2 j.down by
      exact Module.Basis.reindex_apply
        (dwzQ6CoupledBasis K 2) Equiv.ulift.symm j]
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne G0 2 a
      (dwzQ6CoupledCoordGrade 2 j.down) (Ne.symm hne)
    exact Submodule.subset_span ⟨j.down, rfl, rfl⟩
  have houter :=
    mme_primary_hash_family_sharedZ_outer_extraction_exact
      G0 family (mme_dwz_q6_explicit_coupled_four_block_support
        (K := K))
  have hextractZ : extract 2 =
      ∑ a : Fin A, (post a).comp
        (gradedAddressProj G0 n (address a) 2) := by
    apply LinearMap.ext
    intro x
    simp only [extract, post, LinearMap.comp_apply]
    rw [LinearMap.congr_fun houter.2]
    simp only [LinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro a _
    change gradedBigAddSlot A
        (CoupledCTensorPackaging.starObj G0 family) a 2
          (gradedAddressProj G0
            (2 * (50000000 * (20088623 * m))) (exactAddress a).1 2
            ((kronPowLengthEquivPublic
              (coupledObj K 6) hn.symm 2).symm x)) =
      gradedBigAddSlot A
        (CoupledCTensorPackaging.starObj G0 family) a 2
          ((gradedAddressBlockLengthEquivPublic G0 hn.symm
              (exactAddress a).1 2).symm
            (gradedAddressProj G0 n (address a) 2 x))
    exact congrArg
      (gradedBigAddSlot A
        (CoupledCTensorPackaging.starObj G0 family) a 2)
      (LinearMap.congr_fun
        (gradedAddressProj_lengthEquivPublic_symm_comp G0 hn.symm
          (exactAddress a).1 2) x).symm
  have hrouterPow :
      PiTensorProduct.map
          (fun i ↦ kronPowModeMap i (router i) n)
          ((canonicalComponentBlock K 12).kronPow n).t =
        ((coupledObj K 6).kronPow n).t :=
    kronPowModeMap_maps_tensor_public router hrouterTensor n
  have hextractTensor :
      PiTensorProduct.map extract ((coupledObj K 6).kronPow n).t =
        (TensorObj.bigAdd
          (CoupledCTensorPackaging.starObj G0 family)).t := by
    calc
      _ = PiTensorProduct.map
          (CoupledCTensorPackaging.outerExtractionMap G0 family)
          (PiTensorProduct.map
            (fun i ↦
              (kronPowLengthEquivPublic
                (coupledObj K 6) hn.symm i).symm.toLinearMap)
            ((coupledObj K 6).kronPow n).t) := by
              rw [PiTensorProduct.map_comp]
              rfl
      _ = PiTensorProduct.map
          (CoupledCTensorPackaging.outerExtractionMap G0 family)
          ((coupledObj K 6).kronPow
            (2 * (50000000 * (20088623 * m)))).t := by
              rw [kronPowLengthEquivPublic_symm_maps_tensor]
      _ = _ := houter.1
  exact mme_dwz_q6_112_router_projector_descent_poly
    m (coupledObj K 6)
    (TensorObj.bigAdd (CoupledCTensorPackaging.starObj G0 family)) G0
    cZ targetGrade router label hrouterZ' htranslate
    exactAddress address haddress post extract hGzero hextractZ
    hrouterPow hextractTensor

end MME.DWZComponentRestriction

theorem solution
    {K : Type u} [Field K] (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (50000000 * (20088623 * m))
      (21015 * (20088623 * m))
      (49978985 * (20088623 * m)) A H) :
    TensorObj.Restrict
      (TensorObj.bigAdd
        (CoupledCTensorPackaging.starObj
          (MME.DWZComponentRestriction.dwzQ6CoupledGrading K) family))
      (MME.DWZComponentRestriction.restrictedComponentPower K
        (12 : Fin 15) m) :=
  MME.DWZComponentRestriction.outerRestrictProof m A H family
