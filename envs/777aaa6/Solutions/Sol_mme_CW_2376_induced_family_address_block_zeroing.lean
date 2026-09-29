-- Prove2me | solution 1 for mme_CW_2376_induced_family_address_block_zeroing
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T18:54:04.745935+00:00
-- url     : https://prove2.me/submissions/da9fc490-3dd7-4ffc-8c7e-7a08095d8c38

import Theorems.Thm_mme_induced_graded_address_blocks_restrict
import Definitions.Def_mme_CW_2376_profile_induced_family

open MME

set_option autoImplicit false

universe u

theorem solution
    {K : Type u} [Field K]
    (cert : CWSquareFiveGradeCertificate K 6)
    (m : ℕ) (F : Finset (CW2376ExactProfileAddress m))
    (hF : CW2376InducedModeDisjoint F) :
    ∃ e : Fin F.card ≃ F,
      TensorObj.Restrict
        (TensorObj.bigAdd
          (fun j => cw2376ExactAddressBlock cert (e j).1))
        ((TensorObj.kron (CWObj K 6) (CWObj K 6)).kronPow
          (cw2376ProfileLength m)) := by
  classical
  let e : Fin F.card ≃ F := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin F).symm
  let A : Fin F.card → Fin 3 →
      Fin (cw2376ProfileLength m) → Fin 5 :=
    fun j => (e j).1.1
  have hinduced : ∀ js : Fin 3 → Fin F.card,
      (∀ r : Fin (cw2376ProfileLength m),
        cert.grading.blockTensor (fun i => A (js i) i r) ≠ 0) →
      ∃ j : Fin F.card, js = fun _ => j := by
    intro js hnonzero
    have hsupported : CW2376CoordinatewiseSupported
        (cw2376MixedAddress
          (e (js 0)).1.1 (e (js 1)).1.1 (e (js 2)).1.1) := by
      intro r
      change
        ((e (js 0)).1.1 0 r).val +
          ((e (js 1)).1.1 1 r).val +
          ((e (js 2)).1.1 2 r).val = 4
      by_contra hsum
      apply hnonzero r
      have hz := cert.support
        ((e (js 0)).1.1 0 r)
        ((e (js 1)).1.1 1 r)
        ((e (js 2)).1.1 2 r) hsum
      have htype : (fun i => A (js i) i r) =
          cwSquareBlockType
            ((e (js 0)).1.1 0 r)
            ((e (js 1)).1.1 1 r)
            ((e (js 2)).1.1 2 r) := by
        funext i
        fin_cases i <;> rfl
      exact @Eq.ndrec (Fin 3 → Fin 5)
        (cwSquareBlockType
          ((e (js 0)).1.1 0 r)
          ((e (js 1)).1.1 1 r)
          ((e (js 2)).1.1 2 r))
        (fun σ => cert.grading.blockTensor σ = 0)
        hz
        (fun i => A (js i) i r)
        htype.symm
    obtain ⟨h01e, h12e⟩ :=
      hF.2 (e (js 0)) (e (js 1)) (e (js 2)) hsupported
    have h01 : js 0 = js 1 := e.injective h01e
    have h12 : js 1 = js 2 := e.injective h12e
    refine ⟨js 0, ?_⟩
    funext i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact (h01.trans h12).symm
  refine ⟨e, ?_⟩
  have hzeroing :=
    mme_induced_graded_address_blocks_restrict cert.grading A hinduced
  simpa [A, gradedAddressBlock, cw2376ExactAddressBlock] using hzeroing
