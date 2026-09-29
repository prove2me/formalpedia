-- Prove2me | solution 1 for mme_dwz_q6_211_outerExtractionMap_mode1_vanishes_on_disallowed_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T13:27:55.57472+00:00
-- url     : https://prove2.me/submissions/92d86a4e-695f-4723-91dc-c3ace79b2714

import Theorems.Thm_mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
import Definitions.Def_mme_kron_pow_word_reindex
import Mathlib.Tactic

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct BigOperators Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

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
        MME.DWZTable2Counts.split (14 : Fin 15) a * m) :
    outerExtractionMap (dwzQ6CoupledGrading K) family 1
        (kronPowModeBasis (coupledObj K 6) 1
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm)
          (2 * (1036722900000000 * m))
          (PowIndex.ofFun (2 * (1036722900000000 * m))
            (fun r ↦ ULift.up (coord (PowIndex.get _ w r))))) =
      0 := by
  let n : ℕ := 2 * (1036722900000000 * m)
  let decoded : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) n :=
    PowIndex.ofFun n
      (fun r ↦ ULift.up (coord (PowIndex.get n w r)))
  apply mme_primary_hash_family_outerExtractionMap_modeOne_profile_zero
    family decoded
  intro hprofile
  apply hnot
  intro a
  rw [Fintype.card_subtype]
  have htranslate : ∀ r : Fin n,
      dwzQ6CoupledCoordGrade 1
          (PowIndex.get n decoded r).down =
        (PowIndex.get n w r).leftGrade := by
    intro r
    rw [show PowIndex.get n decoded r =
        ULift.up (coord (PowIndex.get n w r)) by
      simp [decoded, PowIndex.get_ofFun]]
    have hr := hcoord (PowIndex.get n w r)
    rcases hc : coord (PowIndex.get n w r) with x | x
    · simpa [dwzQ6CoupledCoordGrade, hc] using hr.symm
    · simpa [dwzQ6CoupledCoordGrade, hc] using hr.symm
  calc
    (Finset.univ.filter (fun r : Fin n ↦
        (PowIndex.get n w r).leftGrade = a)).card =
        (Finset.univ.filter (fun r : Fin n ↦
          dwzQ6CoupledCoordGrade 1
            (PowIndex.get n decoded r).down = a)).card := by
      congr 1
      ext r
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        htranslate r]
    _ = cwQ6CoupledMarginalMultiplicity
          (1036722900000000 * m) L G 1 a := hprofile a
    _ = MME.DWZTable2Counts.split (14 : Fin 15) a * m := by
      fin_cases a <;>
        simp [cwQ6CoupledMarginalMultiplicity,
          MME.DWZTable2Counts.split]
