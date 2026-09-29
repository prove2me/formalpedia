-- Prove2me | solution 1 for mme_CW_q6_common_halving_paired_oriented_component_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:45:37.885159+00:00
-- url     : https://prove2.me/submissions/06f64a26-7de7-4aa1-b31c-866d1c78c355

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_isomorphisms
import Theorems.Thm_mme_MMObj_permObj_cyclic_sq
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_kronFin_respects_iso
import Definitions.Def_mme_mmobj_mul
import Mathlib.Tactic

open MME PiTensorProduct BigOperators Module
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MME.PairedOrientedPackaging

variable {K : Type u} [Field K]

private theorem supported_eq_one_of_four
    {sigma : Fin 3 → Fin 3}
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    sigma = ![0, 0, 0] ∨ sigma = ![1, 1, 1] ∨
      sigma = ![0, 1, 2] ∨ sigma = ![1, 0, 2] := by
  rcases hsigma with h | h | h | h
  · left
    funext i
    fin_cases i <;> simp_all
  · right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; left
    funext i
    fin_cases i <;> simp_all
  · right; right; right
    funext i
    fin_cases i <;> simp_all

private theorem baseBlockIso
    (sigma : Fin 3 → Fin 3)
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    TensorObj.Isomorphic
      (MMObj K (localM sigma) (localN sigma) (localP sigma))
      ((dwzQ6CoupledGrading K).blockSubtensor sigma) := by
  obtain ⟨h000, h111, h012, h102⟩ :=
    mme_dwz_q6_explicit_coupled_four_block_isomorphisms (K := K)
  rcases supported_eq_one_of_four hsigma with h | h | h | h
  · subst sigma
    simpa [localM, localN, localP] using h000
  · subst sigma
    simpa [localM, localN, localP] using h111
  · subst sigma
    simpa [localM, localN, localP] using h012
  · subst sigma
    simpa [localM, localN, localP] using h102

private theorem leftLocalBlockIso
    (sigma : Fin 3 → Fin 3)
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    TensorObj.Isomorphic
      (MMObj K (localN sigma) (localP sigma) (localM sigma))
      ((leftGrading (K := K)).blockSubtensor
        (fun i ↦ sigma ((cyclicPerm.trans cyclicPerm).symm i))) := by
  let e := cyclicPerm.trans cyclicPerm
  have hbase := baseBlockIso (K := K) sigma hsigma
  have hperm := TensorObj.permObj_isomorphic e hbase
  have hmm := mme_MMObj_permObj_cyclic_sq
    (K := K) (localM sigma) (localN sigma) (localP sigma)
  have hblock := TensorObj.TypeGrading.permObjGrading_blockSubtensor_iso
    (dwzQ6CoupledGrading K) e sigma
  exact hmm.symm.trans (hperm.trans hblock.symm)

private theorem rightLocalBlockIso
    (sigma : Fin 3 → Fin 3)
    (hsigma :
      (sigma 0 = 0 ∧ sigma 1 = 0 ∧ sigma 2 = 0) ∨
      (sigma 0 = 1 ∧ sigma 1 = 1 ∧ sigma 2 = 1) ∨
      (sigma 0 = 0 ∧ sigma 1 = 1 ∧ sigma 2 = 2) ∨
      (sigma 0 = 1 ∧ sigma 1 = 0 ∧ sigma 2 = 2)) :
    TensorObj.Isomorphic
      (MMObj K (localP sigma) (localM sigma) (localN sigma))
      ((rightGrading (K := K)).blockSubtensor
        (fun i ↦ sigma (cyclicPerm.symm i))) := by
  have hbase := baseBlockIso (K := K) sigma hsigma
  have hperm := TensorObj.permObj_isomorphic cyclicPerm hbase
  have hmm := MMObj_permObj_cyclic
    (K := K) (localM sigma) (localN sigma) (localP sigma)
  have hblock := TensorObj.TypeGrading.permObjGrading_blockSubtensor_iso
    (dwzQ6CoupledGrading K) cyclicPerm sigma
  exact hmm.symm.trans (hperm.trans hblock.symm)

theorem component_isomorphic
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) :
    TensorObj.Isomorphic
      (MMObj K
        (componentM family halving p)
        (componentN family halving p)
        (componentP family halving p))
      (componentObj (K := K) family halving p) := by
  let aL : Fin N → ℕ := fun r ↦ localN (leftType family halving p r)
  let bL : Fin N → ℕ := fun r ↦ localP (leftType family halving p r)
  let cL : Fin N → ℕ := fun r ↦ localM (leftType family halving p r)
  let aR : Fin N → ℕ := fun r ↦ localP (rightType family halving p r)
  let bR : Fin N → ℕ := fun r ↦ localM (rightType family halving p r)
  let cR : Fin N → ℕ := fun r ↦ localN (rightType family halving p r)
  have hpointL : ∀ r : Fin N,
      TensorObj.Isomorphic
        (MMObj K (aL r) (bL r) (cL r))
        ((leftGrading (K := K)).blockSubtensor
          (fun i ↦ leftType family halving p r
            ((cyclicPerm.trans cyclicPerm).symm i))) := by
    intro r
    exact leftLocalBlockIso (K := K) _
      ((family.entry p).2.1 (halving.position (Sum.inl r)))
  have hpointR : ∀ r : Fin N,
      TensorObj.Isomorphic
        (MMObj K (aR r) (bR r) (cR r))
        ((rightGrading (K := K)).blockSubtensor
          (fun i ↦ rightType family halving p r (cyclicPerm.symm i))) := by
    intro r
    exact rightLocalBlockIso (K := K) _
      ((family.entry p).2.1 (halving.position (Sum.inr r)))
  have hfamilyL := mme_kronFin_respects_iso N
    (fun r ↦ MMObj K (aL r) (bL r) (cL r))
    (fun r ↦ (leftGrading (K := K)).blockSubtensor
      (fun i ↦ leftType family halving p r
        ((cyclicPerm.trans cyclicPerm).symm i))) hpointL
  have hfamilyR := mme_kronFin_respects_iso N
    (fun r ↦ MMObj K (aR r) (bR r) (cR r))
    (fun r ↦ (rightGrading (K := K)).blockSubtensor
      (fun i ↦ rightType family halving p r (cyclicPerm.symm i))) hpointR
  have hmmL := mme_kronFin_MMObj_iso (K := K) N aL bL cL
  have hmmR := mme_kronFin_MMObj_iso (K := K) N aR bR cR
  have hL : TensorObj.Isomorphic
      (MMObj K (∏ r, aL r) (∏ r, bL r) (∏ r, cL r))
      (gradedAddressBlock (leftGrading (K := K))
        (leftAddress family halving p)) := by
    simpa [gradedAddressBlock, leftAddress, leftType] using
      hmmL.symm.trans hfamilyL
  have hR : TensorObj.Isomorphic
      (MMObj K (∏ r, aR r) (∏ r, bR r) (∏ r, cR r))
      (gradedAddressBlock (rightGrading (K := K))
        (rightAddress family halving p)) := by
    simpa [gradedAddressBlock, rightAddress, rightType] using
      hmmR.symm.trans hfamilyR
  have hkron := TensorQ.mul_respects_iso hL hR
  have hmm := MMObj_kron_iso (K := K)
    (∏ r, aL r) (∏ r, bL r) (∏ r, cL r)
    (∏ r, aR r) (∏ r, bR r) (∏ r, cR r)
  simpa [componentObj, componentM, componentN, componentP,
    aL, bL, cL, aR, bR, cR] using hmm.symm.trans hkron

private theorem prod_if_eq
    (q R : ℕ) (f : Fin R → Fin 3) (r : Fin 3) :
    (∏ j : Fin R, if f j = r then q else 1) =
      q ^ (Finset.univ.filter (fun j : Fin R ↦ f j = r)).card := by
  classical
  rw [← Finset.prod_filter]
  simp

private theorem local_volume_indicator (sigma : Fin 3 → Fin 3) :
    localM sigma * localN sigma * localP sigma =
      (if sigma 2 = 0 then 6 else 1) *
      (if sigma 2 = 1 then 6 else 1) *
      (if sigma 2 = 2 then 36 else 1) := by
  generalize hz : sigma 2 = z
  fin_cases z <;> simp [localM, localN, localP, hz]

theorem component_common_volume
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) :
    componentM family halving p *
        componentN family halving p *
        componentP family halving p =
      6 ^ (4 * G + 2 * L) := by
  classical
  let leftVol : Fin N → ℕ := fun r ↦
    localM (leftType family halving p r) *
      localN (leftType family halving p r) *
      localP (leftType family halving p r)
  let rightVol : Fin N → ℕ := fun r ↦
    localM (rightType family halving p r) *
      localN (rightType family halving p r) *
      localP (rightType family halving p r)
  have hrearrange :
      componentM family halving p *
          componentN family halving p *
          componentP family halving p =
        (∏ r : Fin N, leftVol r) * (∏ r : Fin N, rightVol r) := by
    simp only [componentM, componentN, componentP, leftVol, rightVol,
      Finset.prod_mul_distrib]
    ac_rfl
  rw [hrearrange]
  have hsplit :
      (∏ r : Fin N, leftVol r) * (∏ r : Fin N, rightVol r) =
        ∏ j : Fin (2 * N),
          localM (fun i ↦ (family.entry p).1 i j) *
          localN (fun i ↦ (family.entry p).1 i j) *
          localP (fun i ↦ (family.entry p).1 i j) := by
    let volAt : Fin (2 * N) → ℕ := fun j ↦
      localM (fun i ↦ (family.entry p).1 i j) *
      localN (fun i ↦ (family.entry p).1 i j) *
      localP (fun i ↦ (family.entry p).1 i j)
    change
      (∏ r : Fin N, volAt (halving.position (Sum.inl r))) *
          (∏ r : Fin N, volAt (halving.position (Sum.inr r))) =
        ∏ j : Fin (2 * N), volAt j
    calc
      _ = ∏ x : Fin N ⊕ Fin N, volAt (halving.position x) := by
        exact (Fintype.prod_sum_type
          (fun x : Fin N ⊕ Fin N ↦ volAt (halving.position x))).symm
      _ = ∏ j : Fin (2 * N), volAt j :=
        halving.position.prod_comp volAt
  rw [hsplit]
  simp_rw [local_volume_indicator]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_if_eq, prod_if_eq, prod_if_eq]
  rw [(family.entry p).2.2 2 0, (family.entry p).2.2 2 1,
    (family.entry p).2.2 2 2]
  simp [cwQ6CoupledMarginalMultiplicity]
  calc
    6 ^ L * 6 ^ L * 36 ^ (2 * G) =
        6 ^ (L + L) * 36 ^ (2 * G) := by rw [pow_add]
    _ =
        6 ^ (L + L) * (6 ^ 2) ^ (2 * G) := by
      rw [show (36 : ℕ) = 6 ^ 2 by norm_num]
    _ = 6 ^ (L + L) * 6 ^ (2 * (2 * G)) := by
      rw [← pow_mul]
    _ = 6 ^ ((L + L) + 2 * (2 * G)) := by
      simp only [pow_add, mul_assoc]
    _ = 6 ^ (4 * G + 2 * L) := by
      congr 1
      omega

end MME.PairedOrientedPackaging

open MME

theorem solution
    {K : Type u} [Field K]
    {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (p : Fin A × Fin H) :
    TensorObj.Isomorphic
        (MMObj K
          (MME.PairedOrientedPackaging.componentM family halving p)
          (MME.PairedOrientedPackaging.componentN family halving p)
          (MME.PairedOrientedPackaging.componentP family halving p))
        (MME.PairedOrientedPackaging.componentObj
          (K := K) family halving p) ∧
      MME.PairedOrientedPackaging.componentM family halving p *
          MME.PairedOrientedPackaging.componentN family halving p *
          MME.PairedOrientedPackaging.componentP family halving p =
        6 ^ (4 * G + 2 * L) := by
  exact ⟨MME.PairedOrientedPackaging.component_isomorphic
      (K := K) family halving p,
    MME.PairedOrientedPackaging.component_common_volume
      family halving p⟩
