-- Prove2me | solution 1 for mme_stothers_general_address_group_by_ordered_grade_types
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-09T04:45:13.802206+00:00
-- url     : https://prove2.me/submissions/a62aa992-9c02-49de-946e-2e05d787a046

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_general_outer_profile
import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso

open MME BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ) (m : ℕ)
    (a : MME.StothersFourth.GenExactOuterAddress base m) :
    let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
      classical
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
        (Fintype.equivFin (Fin 3 → Fin 9))
    TensorObj.Isomorphic
      (gradedAddressBlock
        (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
      (TensorObj.kronFin 729 (fun s ↦
        ((MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
          (e.symm s)).kronPow
            (MME.StothersFourth.genJointMultiplicity base m (e.symm s)))) := by
  classical
  let e : (Fin 3 → Fin 9) ≃ Fin 729 := by
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.reducePow] using
      (Fintype.equivFin (Fin 3 → Fin 9))
  let X : Fin 729 → TensorObj K 3 := fun s ↦
    (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockSubtensor
      (e.symm s)
  let w : Fin (MME.StothersFourth.genOuterLength base m) → Fin 729 :=
    fun j ↦ e (MME.StothersFourth.genAddressType a.1 j)
  let multiplicity : Fin 729 → ℕ := fun s ↦
    MME.StothersFourth.genJointMultiplicity base m (e.symm s)
  have hcard : ∀ s : Fin 729,
      Fintype.card {j : Fin (MME.StothersFourth.genOuterLength base m) //
        w j = s} = multiplicity s := by
    intro s
    rw [Fintype.card_subtype]
    simpa only [w, multiplicity, e, Equiv.eq_symm_apply] using
      a.2 (e.symm s)
  have hgroup := mme_kronFin_group_by_exact_fibers_iso X w multiplicity hcard
  have hAT : ∀ k : Fin (MME.StothersFourth.genOuterLength base m),
      MME.StothersFourth.genAddressType a.1 k = fun i ↦ a.1 i k := fun _ ↦ rfl
  simpa only [gradedAddressBlock, X, w, multiplicity,
    hAT, Equiv.symm_apply_apply] using hgroup
