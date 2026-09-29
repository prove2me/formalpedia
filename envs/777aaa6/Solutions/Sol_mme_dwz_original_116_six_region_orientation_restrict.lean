-- Prove2me | solution 1 for mme_dwz_original_116_six_region_orientation_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:01:59.504498+00:00
-- url     : https://prove2.me/submissions/ce6655d8-c33c-4ac7-8377-c3cb8b82d7be

import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_orbit
import Theorems.Thm_mme_sixSymmetrization_kronFin_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_dwz_positive_116_original_profile_regional_restrict
import Mathlib.Tactic

open BigOperators MME MME.TensorObj
open scoped Classical
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1Orientation

theorem cyclic_kronFin_isomorphic {K : Type u} [Field K] {n : ℕ}
    (A : Fin n → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (kronFin n A))
      (kronFin n (fun r ↦ cyclicSymmetrization (A r))) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [cyclicSymmetrization_eq_public_perm, TensorQ.toQ_kron,
    mme_toQ_kronFin, ← TensorQ.permAut_toQ, map_prod, Finset.prod_mul_distrib]

/-- Apply the mode rotations to the projected tensor itself, so its prescribed
Z filter is transported to the corresponding mode without changing its profile. -/
noncomputable def regionRotation {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : Fin 3 → TensorObj K 3 :=
  ![A 0, permObj cyclicPerm (A 1),
    permObj (cyclicPerm.trans cyclicPerm) (A 2)]

noncomputable def asymmetricRegionalTensor {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) : TensorObj K 3 :=
  kronFin 3 (fun r ↦ kron (regionRotation A r)
    (permObj swapFirstTwoPerm (regionRotation A r)))

theorem rotated_six_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (r : Fin 3) :
    Isomorphic (sixSymmetrization (regionRotation A r)) (sixSymmetrization (A r)) := by
  fin_cases r
  · exact Isomorphic.refl _
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 1)).1
  · exact (mme_sixSymmetrization_isomorphic_cyclic_orbit (A 2)).2

/-- Claims 7.2--7.3's six-region rearrangement, before extraction of child tensors. -/
theorem asymmetric_cyclic_isomorphic {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) :
    Isomorphic (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (kronFin 3 A)) := by
  apply Isomorphic.trans (cyclic_kronFin_isomorphic _)
  apply Isomorphic.trans _ (mme_sixSymmetrization_kronFin_isomorphic A)
  apply TensorQ.toQ_eq_iff.mp
  rw [mme_toQ_kronFin, mme_toQ_kronFin]
  apply Finset.prod_congr rfl
  intro r _
  apply TensorQ.toQ_eq_iff.mpr
  exact (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
    (regionRotation A r)).symm.trans (rotated_six_isomorphic A r)

theorem asymmetric_regional_restrict {K : Type u} [Field K]
    (A : Fin 3 → TensorObj K 3) (T : TensorObj K 3)
    (h : TensorObj.Restrict (kronFin 3 A) T) :
    TensorObj.Restrict (cyclicSymmetrization (asymmetricRegionalTensor A)) (sixSymmetrization T) :=
  (asymmetric_cyclic_isomorphic A).1.trans (mme_sixSymmetrization_restrict h)

open MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent116

theorem original116_asymmetric_restrict {K : Type u} [Field K] (q m : ℕ) :
    let A := fun r : Fin 3 ↦ prescribedZPower
      (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
      (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
      (regionalProfile r) (regionalWeight r * m)
    TensorObj.Restrict (cyclicSymmetrization (asymmetricRegionalTensor A))
      (sixSymmetrization (prescribedZPower
        (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
        (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
        parentProfile m)) := by
  dsimp only
  exact asymmetric_regional_restrict _ _
    (mme_dwz_positive_116_original_profile_regional_restrict q m).2.2.2

end MME.DWZC1Orientation

open MME.DWZRestrictedValue MME.DWZComponentRestriction MME.CompleteSplit.CWFourth MME.StothersFourth MME.DWZPositiveComponent116
theorem solution {K : Type u} [Field K] :
    (∀ A : Fin 3 → TensorObj K 3,
      let B : Fin 3 → TensorObj K 3 := ![A 0, permObj cyclicPerm (A 1),
        permObj (cyclicPerm.trans cyclicPerm) (A 2)]
      TensorObj.Isomorphic
        (cyclicSymmetrization (kronFin 3 (fun r ↦
          kron (B r) (permObj swapFirstTwoPerm (B r)))))
        (sixSymmetrization (kronFin 3 A))) ∧
    ∀ q m : ℕ,
      let A := fun r : Fin 3 ↦ prescribedZPower
        (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
        (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
        (regionalProfile r) (regionalWeight r * m)
      let B : Fin 3 → TensorObj K 3 := ![A 0, permObj cyclicPerm (A 1),
        permObj (cyclicPerm.trans cyclicPerm) (A 2)]
      TensorObj.Restrict
        (cyclicSymmetrization (kronFin 3 (fun r ↦
          kron (B r) (permObj swapFirstTwoPerm (B r)))))
        (sixSymmetrization (prescribedZPower
          (cwFourthConstituent K q 1 1 6) (constituentBasis K q 1 1 6 2)
          (fun a : LiftedCoarseCoordinate.{u} q 6 ↦ cwSquarePairGrade q a.down.val.1)
          parentProfile m)) := by
  constructor
  · exact MME.DWZC1Orientation.asymmetric_cyclic_isomorphic
  · exact MME.DWZC1Orientation.original116_asymmetric_restrict
