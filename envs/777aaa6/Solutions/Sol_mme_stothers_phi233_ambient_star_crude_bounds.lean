-- Prove2me | solution 1 for mme_stothers_phi233_ambient_star_crude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-04T09:19:33.781576+00:00
-- url     : https://prove2.me/submissions/31eeb160-09c6-4e54-a8ec-bbe6c8365e6d

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_profile_data

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    let D := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l}
    1 ≤ D ∧ D ≤ 5 ^ (18 * N) := by
  classical
  letI : Fintype (MME.StothersFourth.Phi233.ProfileAddress N) := by
    unfold MME.StothersFourth.Phi233.ProfileAddress
    infer_instance
  letI : Fintype
      (MME.StothersFourth.Phi233.MarginalAddress
        N alpha beta gamma delta) := by
    unfold MME.StothersFourth.Phi233.MarginalAddress
    infer_instance
  let D := ∏ l : Fin 3,
    Nat.card
      {b : MME.StothersFourth.Phi233.MarginalAddress
          N alpha beta gamma delta // b.1 l = a.1.1 l}
  have hpos : ∀ l : Fin 3, 1 ≤
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l} := by
    intro l
    letI : Nonempty
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l} :=
      ⟨⟨a.1, rfl⟩⟩
    exact Nat.card_pos
  have hbound : ∀ l : Fin 3,
      Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l} ≤
        5 ^ (6 * N) := by
    intro l
    calc
      Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l} ≤
          Nat.card
            (MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ ≤ Nat.card (MME.StothersFourth.Phi233.ProfileAddress N) :=
        Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
      _ = 5 ^ (6 * N) := by
        simp only [MME.StothersFourth.Phi233.ProfileAddress,
          Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
        rw [← pow_mul]
        congr 1
        omega
  constructor
  · dsimp only [D]
    exact Fintype.one_le_prod hpos
  · dsimp only [D]
    calc
      (∏ l : Fin 3,
          Nat.card
            {b : MME.StothersFourth.Phi233.MarginalAddress
                N alpha beta gamma delta // b.1 l = a.1.1 l}) ≤
          ∏ _l : Fin 3, 5 ^ (6 * N) := by
        exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
          (fun l _ ↦ hbound l)
      _ = 5 ^ (18 * N) := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        rw [← pow_mul]
        congr 1
        omega
