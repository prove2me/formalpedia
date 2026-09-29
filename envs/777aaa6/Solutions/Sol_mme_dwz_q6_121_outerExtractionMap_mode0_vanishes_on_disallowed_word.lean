-- Prove2me | solution 1 for mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:00:28.738209+00:00
-- url     : https://prove2.me/submissions/00234021-6d66-4691-8d48-d6c8055e7710

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data
import Definitions.Def_mme_dwz_q6_coupled_explicit_grading
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_component_disallowed_word_mismatches_profile
import Theorems.Thm_mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

/-- The mode-zero shared-Z outer extraction kills every row-121 canonical
word whose left-grade histogram fails the prescribed balanced profile, after
the row router's coordinate decoding into the unpermuted coupled basis. -/
theorem mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H)
    (coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6))
    (hcoord : ∀ p,
      p.leftGrade =
        Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
          (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p))
    (w : PowIndex (LiftedCoarsePair.{u} 6 1)
      (2 * (1036722900000000 * m)))
    (hnot : ¬ ∀ a : Fin 3,
      Fintype.card
          {r : Fin (2 * (1036722900000000 * m)) //
            (PowIndex.get _ w r).leftGrade = a} =
        MME.DWZTable2Counts.split (13 : Fin 15) a * m) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 0
        (kronPowModeBasis (coupledObj K 6) 0
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
          (2 * (1036722900000000 * m))
          (PowIndex.ofFun (2 * (1036722900000000 * m))
            (fun r ↦ ULift.up (coord (PowIndex.get _ w r))))) =
      0 := by
  let n : ℕ := 2 * (1036722900000000 * m)
  let grading := dwzQ6CoupledGrading K
  let b0 : Basis (ULift.{u} (Fin 6 ⊕ Fin 6)) K
      ((coupledObj K 6).V 0) :=
    (Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm
  let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 := fun j ↦
    dwzQ6CoupledCoordGrade 0 j.down
  let decoded : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) n :=
    PowIndex.ofFun n
      (fun r ↦ ULift.up (coord (PowIndex.get n w r)))
  have hGzero : ∀ (a : Fin 3) (j : ULift.{u} (Fin 6 ⊕ Fin 6)),
      grade j ≠ a → grading.blockProj 0 a (b0 j) = 0 := by
    intro a j hne
    rw [show b0 j = dwzQ6CoupledBasis K 0 j.down by
      exact Module.Basis.reindex_apply
        (dwzQ6CoupledBasis K 0) Equiv.ulift.symm j]
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne grading 0 a
      (dwzQ6CoupledCoordGrade 0 j.down) (Ne.symm hne)
    exact Submodule.subset_span ⟨j.down, rfl, rfl⟩
  have hterm : ∀ p : Fin A × Fin H,
      outerExtractionSummand grading family 0 p
          (kronPowModeBasis (coupledObj K 6) 0 b0 n decoded) = 0 := by
    intro p
    let address := componentAddress family p.1 p.2
    have htarget : ∀ a : Fin 3,
        Fintype.card {r : Fin n // address 0 r = a} =
          MME.DWZTable2Counts.split (13 : Fin 15) a * m := by
      intro a
      have hprofile := (family.entry p).2.2 0 a
      rw [← componentAddress_eq_entry family p.1 p.2] at hprofile
      rw [Fintype.card_subtype]
      calc
        (Finset.univ.filter (fun r : Fin n ↦ address 0 r = a)).card =
            cwQ6CoupledMarginalMultiplicity
              (1036722900000000 * m) L G 0 a := hprofile
        _ = MME.DWZTable2Counts.split (13 : Fin 15) a * m := by
          fin_cases a <;>
            simp [cwQ6CoupledMarginalMultiplicity,
              MME.DWZTable2Counts.split]
    have htranslate : ∀ p : LiftedCoarsePair.{u} 6 1,
        p.leftGrade = grade (ULift.up (coord p)) := by
      intro q
      have hq := hcoord q
      rcases h : coord q with x | x
      · simpa [grade, dwzQ6CoupledCoordGrade, h] using hq
      · simpa [grade, dwzQ6CoupledCoordGrade, h] using hq
    have hmismatch : ∃ r : Fin n,
        grade (PowIndex.get n decoded r) ≠ address 0 r := by
      have hm := mme_dwz_component_disallowed_word_mismatches_profile
        (s := (13 : Fin 15)) (m := m) w hnot
        (fun r ↦ address 0 r) htarget
        (fun q ↦ grade (ULift.up (coord q))) htranslate
      simpa [decoded, PowIndex.get_ofFun] using hm
    have hproj :=
      mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
        grading 0 b0 grade hGzero n address decoded hmismatch
    change gradedBigAddSlot A (starObj grading family) p.1 0
        (componentInclusion grading family p.1 p.2 0
          (gradedAddressProj grading n address 0
            (kronPowModeBasis (coupledObj K 6) 0 b0 n decoded))) = 0
    rw [hproj]
    have hin :
        componentInclusion grading family p.1 p.2 0
            (0 : (componentObj grading family p.1 p.2).V 0) = 0 :=
      (componentInclusion grading family p.1 p.2 0).map_zero
    have hout : gradedBigAddSlot A (starObj grading family) p.1 0
          (0 : (starObj grading family p.1).V 0) = 0 :=
      (gradedBigAddSlot A (starObj grading family) p.1 0).map_zero
    simpa [address, componentObj] using
      (congrArg (gradedBigAddSlot A (starObj grading family) p.1 0) hin).trans hout
  change outerExtractionMap grading family 0
      (kronPowModeBasis (coupledObj K 6) 0 b0 n decoded) = 0
  simp only [outerExtractionMap, LinearMap.sum_apply]
  exact Finset.sum_eq_zero (fun p _ ↦ hterm p)

theorem solution
    {K : Type u} [Field K]
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (1036722900000000 * m) L G A H)
    (coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6))
    (hcoord : ∀ p,
      p.leftGrade =
        Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
          (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p))
    (w : PowIndex (LiftedCoarsePair.{u} 6 1)
      (2 * (1036722900000000 * m)))
    (hnot : ¬ ∀ a : Fin 3,
      Fintype.card
          {r : Fin (2 * (1036722900000000 * m)) //
            (PowIndex.get _ w r).leftGrade = a} =
        MME.DWZTable2Counts.split (13 : Fin 15) a * m) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 0
        (kronPowModeBasis (coupledObj K 6) 0
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
          (2 * (1036722900000000 * m))
          (PowIndex.ofFun (2 * (1036722900000000 * m))
            (fun r ↦ ULift.up (coord (PowIndex.get _ w r))))) =
      0 :=
  mme_dwz_q6_121_outerExtractionMap_mode0_vanishes_on_disallowed_word
    m L G A H family coord hcoord w hnot
