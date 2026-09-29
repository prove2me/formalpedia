-- Prove2me | solution 1 for mme_induced_mode_choice_certificate_precompose_router_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:55:58.820734+00:00
-- url     : https://prove2.me/submissions/39c8a4f2-3bf7-4e21-9321-e6ad2de852ad

import Definitions.Def_mme_induced_mode_choice_certificate

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {source middle target : TensorObj K 3}
    (router : ∀ i : Fin 3, source.V i →ₗ[K] middle.V i)
    (hrouter : PiTensorProduct.map router source.t = middle.t)
    (cert : InducedModeChoiceCertificate middle target)
    {alpha : Type u} (basisVector : alpha → source.V 2)
    (bad : alpha → Prop)
    (hvanish : ∀ (slot : Fin (cert.slotCount 2)) (a : alpha),
      bad a → cert.modeMap 2 slot (router 2 (basisVector a)) = 0) :
    ∃ pulled : InducedModeChoiceCertificate source target,
      ∀ (slot : Fin (pulled.slotCount 2)) (a : alpha),
        bad a → pulled.modeMap 2 slot (basisVector a) = 0 := by
  have hterm (choice : ∀ i : Fin 3, Fin (cert.slotCount i)) :
      PiTensorProduct.map
          (fun i ↦ (cert.modeMap i (choice i)).comp (router i)) source.t =
        PiTensorProduct.map
          (fun i ↦ cert.modeMap i (choice i)) middle.t := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hrouter]
  let pulled : InducedModeChoiceCertificate source target :=
    { slotCount := cert.slotCount
      modeMap := fun i slot ↦ (cert.modeMap i slot).comp (router i)
      kept := cert.kept
      offSupport := by
        intro choice hchoice
        rw [hterm choice]
        exact cert.offSupport choice hchoice
      targetTensor := by
        rw [cert.targetTensor]
        apply Finset.sum_congr rfl
        intro choice _
        exact (hterm choice.1).symm }
  refine ⟨pulled, ?_⟩
  intro slot a ha
  exact hvanish slot a ha
