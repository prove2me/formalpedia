-- Prove2me | solution 1 for mme_induced_mode_choice_certificate_basisZAllowed_descent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T10:26:31.837026+00:00
-- url     : https://prove2.me/submissions/46d549e8-4a38-4518-87e4-f250152e4ee5

import Mathlib.Tactic
import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_basis_z_allowed_projection
import Theorems.Thm_mme_basisZAllowed_blockSubtensor_inclusion_tensor

open MME Module PiTensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
    {K : Type u} [Field K]
    {T A : TensorObj K 3} {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop)
    [DecidablePred allowed]
    (cert : InducedModeChoiceCertificate T A)
    (hvanish : ∀ (slot : Fin (cert.slotCount 2)) (j : ι),
      ¬ allowed j → cert.modeMap 2 slot (bZ j) = 0) :
    Nonempty (InducedModeChoiceCertificate
      (T.basisZAllowedSubtensor bZ allowed) A) := by
  let G := T.basisZAllowedGrading bZ allowed
  let inclusion : ∀ i : Fin 3,
      (T.basisZAllowedSubtensor bZ allowed).V i →ₗ[K] T.V i :=
    fun i => (G.classOf i 0).subtype
  let projected : ∀ i : Fin 3, T.V i →ₗ[K] T.V i :=
    Function.update (fun _ => LinearMap.id) 2
      (bZ.constr K (fun j => if allowed j then bZ j else 0))
  have hinclusion :
      PiTensorProduct.map inclusion
          (T.basisZAllowedSubtensor bZ allowed).t =
        PiTensorProduct.map projected T.t := by
    simpa only [G, inclusion, projected,
      TensorObj.basisZAllowedSubtensor] using
      (mme_basisZAllowed_blockSubtensor_inclusion_tensor
        T bZ allowed)
  have hprojected (choice : ∀ i : Fin 3, Fin (cert.slotCount i)) :
      (fun i => (cert.modeMap i (choice i)).comp (projected i)) =
        (fun i => cert.modeMap i (choice i)) := by
    funext i
    fin_cases i
    · apply LinearMap.ext
      intro x
      rfl
    · apply LinearMap.ext
      intro x
      rfl
    · apply bZ.ext
      intro j
      change cert.modeMap 2 (choice 2)
          ((bZ.constr K (fun j => if allowed j then bZ j else 0)) (bZ j)) =
        cert.modeMap 2 (choice 2) (bZ j)
      rw [Basis.constr_basis]
      by_cases hj : allowed j
      · simp [hj]
      · simp [hj, hvanish (choice 2) j hj]
  have hterm (choice : ∀ i : Fin 3, Fin (cert.slotCount i)) :
      PiTensorProduct.map
          (fun i => (cert.modeMap i (choice i)).comp (inclusion i))
          (T.basisZAllowedSubtensor bZ allowed).t =
        PiTensorProduct.map (fun i => cert.modeMap i (choice i)) T.t := by
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hinclusion]
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    rw [hprojected choice]
  refine ⟨
    { slotCount := cert.slotCount
      modeMap := fun i slot => (cert.modeMap i slot).comp (inclusion i)
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
