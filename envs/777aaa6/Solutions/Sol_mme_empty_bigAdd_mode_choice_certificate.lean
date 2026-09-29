-- Prove2me | solution 1 for mme_empty_bigAdd_mode_choice_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:15:46.304479+00:00
-- url     : https://prove2.me/submissions/148df485-4282-4320-8ac6-ac4b19167bb7

import Mathlib.Tactic
import Definitions.Def_mme_induced_mode_choice_certificate

open MME

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] (S : TensorObj K 3)
    (B : Fin 0 → TensorObj K 3) :
    Nonempty (InducedModeChoiceCertificate S (TensorObj.bigAdd B)) := by
  refine ⟨{
    slotCount := fun _ ↦ 0
    modeMap := fun _ j ↦ j.elim0
    kept := ∅
    offSupport := ?_
    targetTensor := ?_ }⟩
  · intro choice
    exact (choice 0).elim0
  · change (TensorObj.zeroObj : TensorObj K 3).t = ∑ choice :
        {choice : (∀ _ : Fin 3, Fin 0) // choice ∈ (∅ : Finset (∀ _ : Fin 3, Fin 0))}, _
    simp
    rfl
