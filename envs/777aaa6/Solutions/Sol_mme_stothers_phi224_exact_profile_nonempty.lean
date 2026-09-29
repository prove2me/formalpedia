-- Prove2me | solution 1 for mme_stothers_phi224_exact_profile_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T09:37:32.905256+00:00
-- url     : https://prove2.me/submissions/2cc9f502-1050-494d-b650-e6c1732b78e3

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    Nonempty
      (MME.StothersFourth.Phi224.ExactProfileWord
        N alpha beta gamma delta) := by
  let multiplicity : Fin 9 → ℕ :=
    MME.StothersFourth.Phi224.profileMultiplicity
      alpha beta gamma delta
  have htotal : (∑ r : Fin 9, multiplicity r) = 2 * N := by
    simp [multiplicity,
      MME.StothersFourth.Phi224.profileMultiplicity,
      Fin.sum_univ_succ]
    omega
  have hsumUnit : ∀ _i : PUnit.{1},
      (∑ r : {r : Fin 9 // (PUnit.unit : PUnit.{1}) = PUnit.unit},
        multiplicity r.1) =
        Fintype.card
          {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} := by
    intro i
    let eBeta :
        {r : Fin 9 // (PUnit.unit : PUnit.{1}) = PUnit.unit} ≃ Fin 9 :=
      { toFun := Subtype.val
        invFun := fun r ↦ ⟨r, rfl⟩
        left_inv := fun r ↦ Subtype.ext rfl
        right_inv := fun r ↦ rfl }
    let eAlpha :
        {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} ≃
        Fin (2 * N) :=
      { toFun := Subtype.val
        invFun := fun j ↦ ⟨j, rfl⟩
        left_inv := fun j ↦ Subtype.ext rfl
        right_inv := fun j ↦ rfl }
    calc
      (∑ r : {r : Fin 9 // (PUnit.unit : PUnit.{1}) = PUnit.unit},
          multiplicity r.1) =
          ∑ r : Fin 9, multiplicity r :=
        Fintype.sum_equiv eBeta _ _ (fun _ ↦ rfl)
      _ = 2 * N := htotal
      _ = Fintype.card (Fin (2 * N)) := by simp
      _ = Fintype.card
          {j : Fin (2 * N) // (PUnit.unit : PUnit.{1}) = PUnit.unit} :=
        (Fintype.card_congr eAlpha).symm
  obtain ⟨g, _hgGrade, hgFiber⟩ :=
    mme_fintype_constrained_prescribed_fiber_function_nonempty
      (alpha := Fin (2 * N)) (beta := Fin 9) (iota := PUnit.{1})
      (fun _ ↦ PUnit.unit) (fun _ ↦ PUnit.unit) multiplicity hsumUnit
  refine ⟨⟨g, ?_⟩⟩
  intro r
  rw [← Fintype.card_subtype]
  exact hgFiber r
