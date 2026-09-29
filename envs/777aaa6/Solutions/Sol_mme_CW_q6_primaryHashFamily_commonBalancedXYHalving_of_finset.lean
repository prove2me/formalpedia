-- Prove2me | solution 1 for mme_CW_q6_primaryHashFamily_commonBalancedXYHalving_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:29:53.104782+00:00
-- url     : https://prove2.me/submissions/1d9aae7c-f086-432f-b421-1b9363566543

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_common_paired_halving

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {n L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily (2 * n) L G A H)
    (S : Finset (Fin (2 * (2 * n))))
    (hS : S.card = 2 * n)
    (hfirst : ∀ (p : Fin A × Fin H) (grade : Fin 3),
      (S.filter (fun j ↦ (family.entry p).1 0 j = grade)).card =
        if grade = 0 then n else if grade = 1 then n else 0)
    (hsecond : ∀ (p : Fin A × Fin H) (grade : Fin 3),
      ((Finset.univ \ S).filter
        (fun j ↦ (family.entry p).1 1 j = grade)).card =
        if grade = 0 then n else if grade = 1 then n else 0) :
    Nonempty family.CommonBalancedXYHalving := by
  classical
  let eLeft : Fin (2 * n) ≃ {j : Fin (2 * (2 * n)) // j ∈ S} :=
    Fintype.equivOfCardEq (by simp [hS])
  have hcompl : (Finset.univ \ S).card = 2 * n := by
    rw [Finset.card_sdiff]
    simp only [Finset.card_univ, Fintype.card_fin,
      Finset.inter_eq_left.mpr (Finset.subset_univ S), hS]
    omega
  let eRight : Fin (2 * n) ≃ {j : Fin (2 * (2 * n)) // j ∉ S} :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin]
      rw [Fintype.card_subtype]
      have heq :
          (Finset.univ.filter
            (fun j : Fin (2 * (2 * n)) ↦ j ∉ S)) = Finset.univ \ S := by
        ext j
        simp
      rw [heq, hcompl])
  let position : (Fin (2 * n) ⊕ Fin (2 * n)) ≃ Fin (2 * (2 * n)) :=
    (eLeft.sumCongr eRight).trans (Equiv.sumCompl (fun j ↦ j ∈ S))
  refine ⟨{
    half := n
    even_length := rfl
    position := position
    first_x := ?_
    second_y := ?_ }⟩
  · intro p grade
    let e :
        {j : Fin (2 * n) //
          (family.entry p).1 0 (position (Sum.inl j)) = grade} ≃
        {j : {j : Fin (2 * (2 * n)) // j ∈ S} //
          (family.entry p).1 0 j.1 = grade} :=
      eLeft.subtypeEquiv (fun _ ↦ Iff.rfl)
    rw [Fintype.card_congr e]
    calc
      Fintype.card
          {j : {j : Fin (2 * (2 * n)) // j ∈ S} //
            (family.entry p).1 0 j.1 = grade} =
          Fintype.card
            {j : Fin (2 * (2 * n)) //
              j ∈ S ∧ (family.entry p).1 0 j = grade} :=
        Fintype.card_congr
          (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun j : Fin (2 * (2 * n)) ↦ j ∈ S)
            (fun j ↦ (family.entry p).1 0 j = grade))
      _ = (S.filter
          (fun j ↦ (family.entry p).1 0 j = grade)).card := by
        apply Fintype.card_of_subtype
        intro j
        simp
      _ = _ := hfirst p grade
  · intro p grade
    let e :
        {j : Fin (2 * n) //
          (family.entry p).1 1 (position (Sum.inr j)) = grade} ≃
        {j : {j : Fin (2 * (2 * n)) // j ∉ S} //
          (family.entry p).1 1 j.1 = grade} :=
      eRight.subtypeEquiv (fun _ ↦ Iff.rfl)
    rw [Fintype.card_congr e]
    calc
      Fintype.card
          {j : {j : Fin (2 * (2 * n)) // j ∉ S} //
            (family.entry p).1 1 j.1 = grade} =
          Fintype.card
            {j : Fin (2 * (2 * n)) //
              j ∉ S ∧ (family.entry p).1 1 j = grade} :=
        Fintype.card_congr
          (Equiv.subtypeSubtypeEquivSubtypeInter
            (fun j : Fin (2 * (2 * n)) ↦ j ∉ S)
            (fun j ↦ (family.entry p).1 1 j = grade))
      _ = ((Finset.univ \ S).filter
          (fun j ↦ (family.entry p).1 1 j = grade)).card := by
        apply Fintype.card_of_subtype
        intro j
        simp
      _ = _ := hsecond p grade
