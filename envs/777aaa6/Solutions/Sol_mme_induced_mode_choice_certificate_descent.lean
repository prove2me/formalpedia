-- Prove2me | solution 1 for mme_induced_mode_choice_certificate_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:26:28.255779+00:00
-- url     : https://prove2.me/submissions/5757b990-619d-4efd-b989-b1692f2c0fb8

import Definitions.Def_mme_induced_mode_choice_certificate

open MME PiTensorProduct BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K]
    {source ambient target : TensorObj K 3}
    (cert : InducedModeChoiceCertificate ambient target)
    (inclusion : ∀ i : Fin 3, source.V i →ₗ[K] ambient.V i)
    (project : ∀ i : Fin 3, ambient.V i →ₗ[K] ambient.V i)
    (hinclude : PiTensorProduct.map inclusion source.t =
      PiTensorProduct.map project ambient.t)
    (habsorb : ∀ (i : Fin 3) (slot : Fin (cert.slotCount i)),
      (cert.modeMap i slot).comp (project i) = cert.modeMap i slot) :
    Nonempty (InducedModeChoiceCertificate source target) := by
  have hterm (choice : ∀ i : Fin 3, Fin (cert.slotCount i)) :
      PiTensorProduct.map
          (fun i ↦ (cert.modeMap i (choice i)).comp (inclusion i)) source.t =
        PiTensorProduct.map
          (fun i ↦ cert.modeMap i (choice i)) ambient.t := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hinclude]
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    rw [show
      (fun i ↦ (cert.modeMap i (choice i)).comp (project i)) =
        (fun i ↦ cert.modeMap i (choice i)) by
      funext i
      exact habsorb i (choice i)]
  refine ⟨
    { slotCount := cert.slotCount
      modeMap := fun i slot ↦ (cert.modeMap i slot).comp (inclusion i)
      kept := cert.kept
      offSupport := ?_
      targetTensor := ?_ }⟩
  · intro choice hchoice
    rw [hterm choice]
    exact cert.offSupport choice hchoice
  · rw [cert.targetTensor]
    apply Finset.sum_congr rfl
    intro choice _
    exact (hterm choice.1).symm
