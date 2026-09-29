-- Prove2me | solution 1 for mme_dwz_q6_211_restricted_primary_hash_stars_once_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:29:43.552626+00:00
-- url     : https://prove2.me/submissions/78194f3e-b2b1-44f4-ac5a-ff3efe1e2dfa

import Theorems.Thm_mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
import Theorems.Thm_mme_primary_hash_family_permuted_outer_extraction_exact
import Theorems.Thm_mme_perm_kronPow_mode_equiv_recursive_basis
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support
import Theorems.Thm_mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

theorem solution
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H) :
    TensorObj.Restrict
      (TensorObj.permObj cyclicPerm
        (TensorObj.bigAdd
          (starObj (dwzQ6CoupledGrading K) family)))
      (restrictedComponentPower K (14 : Fin 15) m) := by
  let N : ℕ := 1036722900000000 * m
  obtain ⟨coord, hcoord, _hrow13, ⟨router, hrouter, hrouterZ⟩⟩ :=
    mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
      K (2 * N)
  let extraction : ∀ i : Fin 3,
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
        (2 * N)).V i →ₗ[K]
        (TensorObj.permObj cyclicPerm
          (TensorObj.bigAdd
            (starObj (dwzQ6CoupledGrading K) family))).V i := fun i ↦
    (outerExtractionMap (dwzQ6CoupledGrading K) family
      (cyclicPerm.symm i)).comp
        (TensorObj.permKronPowModeEquiv cyclicPerm
          (coupledObj K 6) i (2 * N)).toLinearMap
  let f : ∀ i : Fin 3,
      ((canonicalComponentBlock K (14 : Fin 15)).kronPow
        (2 * N)).V i →ₗ[K]
        (TensorObj.permObj cyclicPerm
          (TensorObj.bigAdd
            (starObj (dwzQ6CoupledGrading K) family))).V i := fun i ↦
    (extraction i).comp (router i)
  have hextraction :
      PiTensorProduct.map extraction
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
            (2 * N)).t =
        (TensorObj.permObj cyclicPerm
          (TensorObj.bigAdd
            (starObj (dwzQ6CoupledGrading K) family))).t := by
    exact mme_primary_hash_family_permuted_outer_extraction_exact
      (dwzQ6CoupledGrading K) family
      (fun σ h000 h111 h012 h102 ↦
        mme_dwz_q6_explicit_coupled_four_block_support
          σ h000 h111 h012 h102)
      cyclicPerm
  have hfmap :
      PiTensorProduct.map f
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow
            (2 * N)).t =
        (TensorObj.permObj cyclicPerm
          (TensorObj.bigAdd
            (starObj (dwzQ6CoupledGrading K) family))).t := by
    calc
      _ = PiTensorProduct.map extraction
          (PiTensorProduct.map router
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow
              (2 * N)).t) := by
            rw [PiTensorProduct.map_comp]
            rfl
      _ = PiTensorProduct.map extraction
          ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow
            (2 * N)).t := by rw [hrouter]
      _ = _ := hextraction
  let allowed : PowIndex (LiftedCoarsePair.{u} 6 1) (2 * N) → Prop :=
    fun w ↦ ∀ a : Fin 3,
      Fintype.card {r : Fin (2 * N) //
        (PowIndex.get (2 * N) w r).leftGrade = a} =
          MME.DWZTable2Counts.split (14 : Fin 15) a * m
  letI : DecidablePred allowed := Classical.decPred _
  have hrestricted := mme_restrict_basisZAllowedSubtensor_of_vanishes
    ((canonicalComponentBlock K (14 : Fin 15)).kronPow (2 * N))
    (TensorObj.permObj cyclicPerm
      (TensorObj.bigAdd (starObj (dwzQ6CoupledGrading K) family)))
    (kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
      (canonicalComponentZBasis K (14 : Fin 15)) (2 * N))
    allowed f hfmap
  have hv : ∀ w, ¬ allowed w →
      f 2
        (kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
          (canonicalComponentZBasis K (14 : Fin 15)) (2 * N) w) = 0 := by
    intro w hnot
    change extraction 2
        (router 2
          (kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
            (canonicalComponentZBasis K (14 : Fin 15)) (2 * N) w)) = 0
    rw [hrouterZ w]
    change outerExtractionMap (dwzQ6CoupledGrading K) family 1
        (TensorObj.permKronPowModeEquiv cyclicPerm
          (coupledObj K 6) 2 (2 * N)
          (kronPowModeBasis
            (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
            ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
            (2 * N)
            (PowIndex.ofFun (2 * N)
              (fun r ↦ ULift.up (coord (PowIndex.get (2 * N) w r)))))) = 0
    rw [mme_perm_kronPow_mode_equiv_recursive_basis]
    exact mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
      m L G A H family coord hcoord w hnot
  have hr := hrestricted hv
  have hlen : MME.DWZTable2Counts.component (14 : Fin 15) * m =
      2 * N := by
    simp [N, MME.DWZTable2Counts.component]
    ring
  have hsourceEq :
      TensorObj.basisZAllowedSubtensor
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow (2 * N))
          (kronPowModeBasis (canonicalComponentBlock K (14 : Fin 15)) 2
            (canonicalComponentZBasis K (14 : Fin 15)) (2 * N)) allowed =
        restrictedComponentPower K (14 : Fin 15) m := by
    unfold restrictedComponentPower componentPowerProjectionGrading
      componentPowerZBasis componentWordAllowed
      TensorObj.basisZAllowedSubtensor
    rw [hlen]
    rfl
  rw [← hsourceEq]
  exact hr
