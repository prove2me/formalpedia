-- Prove2me | solution 1 for mme_gradedAddressProj_kronPowModeBasis_eq_zero_of_mismatch
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T13:53:46.388941+00:00
-- url     : https://prove2.me/submissions/7885c6f4-857b-4b8c-84d6-ec89966738dc

import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_kron_pow_mode_word_basis
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME Module TensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t : ℕ} {ι : Type u}
    (G : T.TypeGrading t) (i : Fin 3)
    (b : Basis ι K (T.V i)) (grade : ι → Fin t)
    (hzero : ∀ (a : Fin t) (j : ι), grade j ≠ a →
      G.blockProj i a (b j) = 0) :
    ∀ (n : ℕ) (address : Fin 3 → Fin n → Fin t)
      (w : PowIndex ι n),
      (∃ r : Fin n, grade (PowIndex.get n w r) ≠ address i r) →
      gradedAddressProj G n address i
          (kronPowModeBasis T i b n w) = 0 := by
  intro n
  induction n with
  | zero =>
      intro address w hmismatch
      obtain ⟨r, _⟩ := hmismatch
      exact Fin.elim0 r
  | succ n ih =>
      intro address w hmismatch
      rcases w with ⟨j, tail⟩
      rw [kronPowModeBasis]
      calc
        _ = gradedAddressProj G (n + 1) address i
              (b j ⊗ₜ[K] kronPowModeBasis T i b n tail) :=
            congrArg (gradedAddressProj G (n + 1) address i)
              (Module.Basis.tensorProduct_apply'
                b (kronPowModeBasis T i b n) (j, tail))
        _ = 0 := by
          change TensorProduct.map
              (G.blockProj i (address i 0))
              (gradedAddressProj G n
                (fun i' j' ↦ address i' j'.succ) i)
              (b j ⊗ₜ[K] kronPowModeBasis T i b n tail) = 0
          rw [TensorProduct.map_tmul]
          obtain ⟨r, hr⟩ := hmismatch
          revert hr
          refine Fin.cases ?_ (fun r' hr ↦ ?_) r
          · intro hr
            rw [hzero (address i 0) j]
            · simp
            · simpa [PowIndex.get] using hr
          · rw [ih (fun i' j' ↦ address i' j'.succ) tail]
            · simp
            · exact ⟨r', by simpa [PowIndex.get] using hr⟩
