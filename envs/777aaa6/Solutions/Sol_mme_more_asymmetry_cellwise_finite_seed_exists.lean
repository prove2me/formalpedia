-- Prove2me | solution 1 for mme_more_asymmetry_cellwise_finite_seed_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T06:37:21.157628+00:00
-- url     : https://prove2.me/submissions/72a49448-6c5d-4b42-94e6-4936801f8974
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_mme_more_asymmetry_raw_source_compatibility
import Definitions.Def_mme_recursive_yz_child_matrix_data
import Theorems.Thm_mme_more_asymmetry_cellwise_seed_records_exist
import Theorems.Thm_mme_kron_self_kronPow_isomorphic
import Theorems.Thm_mme_kronFin_respects_iso
import Theorems.Thm_mme_CW_fourth_power_rank_and_six_symmetry
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic

open BigOperators MME MME.TensorObj MME.HashExtraction
  MME.RecursiveYZ.Certificate

set_option autoImplicit false
universe u

theorem solution {K : Type u} [Field K] :
    ∃ (D : Data) (A : ∀ j, Stage ((D.hash j)))
    (hraw : MoreAsymmetryRawSourceCompatibility D A K)
    (M : ∀ j, (A j).ChildMM K),
    (∏ j, (M j).dimA) = D.a ∧
    (∏ j, (M j).dimB) = D.b ∧
    (∏ j, (M j).dimC) = D.c ∧
    (∀ j, ((8 ^ (A j).repairExponent : ℕ) : ℝ) ≤ (D.hash j).lower) ∧
    (∏ j, 2 * 8 ^ (A j).repairExponent) ≤ D.repairCopies ∧
    (∀ j, (A j).Budget) ∧
    0 < D.power ∧
    (2401 : ℝ) ^ (6 * D.power) <
      D.rate ((3952233 : ℝ) / 5000000) := by
  obtain ⟨D, A, M, hFactors, hPower, hShape, hDimA, hDimB, hDimC,
      hLower, hRepair, hBudget, hRate⟩ :=
    mme_more_asymmetry_cellwise_seed_records_exist (K := K)
  let S := MME.RecursiveYZ.CWCells.source K 5 2 (2 * D.power)
  let T := MME.StothersFourth.cwFourthObj K 5
  have hTS : TensorObj.Isomorphic (T.kronPow D.power) S := by
    let X : TensorObj K 3 := TensorObj.kron (CWObj K 5) (CWObj K 5)
    have h1 := mme_kron_self_kronPow_isomorphic X D.power
    have h2 := mme_kron_self_kronPow_isomorphic (CWObj K 5) (2 * D.power)
    have hgroup : TensorObj.Isomorphic (T.kronPow D.power)
        ((CWObj K 5).kronPow (2 * (2 * D.power))) := by
      simpa [T, MME.StothersFourth.cwFourthObj, X] using h1.trans h2
    have hexp : 2 * (2 * D.power) = (2 * D.power) * 2 := by omega
    simpa [S, MME.RecursiveYZ.CWCells.source, hexp] using hgroup
  have hFactorsIso := mme_kronFin_respects_iso D.factors
    (fun _ : Fin D.factors => S)
    (fun _ : Fin D.factors => T.kronPow D.power)
    (fun _ => hTS.symm)
  have hFactorsIso6 : TensorObj.Isomorphic
      (TensorObj.kronFin 6 (fun _ : Fin 6 => S))
      (TensorObj.kronFin 6 (fun _ : Fin 6 => T.kronPow D.power)) := by
    rw [← hFactors]
    exact hFactorsIso
  have hSix := (mme_CW_fourth_power_rank_and_six_symmetry (K := K)
    5 D.power hPower).2
  have hComm := mme_sixSymmetrization_kronPow_isomorphic T D.power
  have hAmbient : TensorObj.Isomorphic
      (TensorObj.kronFin 6 (fun _ : Fin 6 => S))
      ((sixSymmetrization T).kronPow D.power) := by
    simpa [TensorObj.kronFin, TensorObj.kronPow] using
      hFactorsIso6.trans (hSix.symm.trans hComm.symm)
  have hraw : MoreAsymmetryRawSourceCompatibility D A K := by
    refine ⟨S, ?_, ?_⟩
    · intro j
      simpa [MME.RecursiveYZ.Certificate.Stage.raw, S,
        (hShape j).1, (hShape j).2] using TensorObj.Restrict.refl S
    · rw [hFactors]
      simpa [T] using hAmbient
  exact ⟨D, A, hraw, M, hDimA, hDimB, hDimC, hLower, hRepair,
    hBudget, hPower, hRate⟩
