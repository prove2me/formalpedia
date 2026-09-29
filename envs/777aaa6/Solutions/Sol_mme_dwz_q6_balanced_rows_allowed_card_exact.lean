-- Prove2me | solution 1 for mme_dwz_q6_balanced_rows_allowed_card_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T09:28:48.664292+00:00
-- url     : https://prove2.me/submissions/a1875529-650b-4141-b6d2-3ddd89c256ba

import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_dwz_q6_balanced_rectangular_product_coordinates
import Theorems.Thm_mme_prescribed_product_alphabet_word_card

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace MME.DWZBalancedRowsAllowedCard

theorem gradeThree_fiber_predicate_iff
    (e : LiftedCoarsePair.{u} 6 3 ≃ Fin 2 × Fin 6)
    (he : ∀ p, p.leftGrade = ![2, 1] (e p).1)
    (N k : ℕ) (w : PowIndex (LiftedCoarsePair.{u} 6 3) N) :
    (∀ a : Fin 3,
      Fintype.card {r : Fin N //
        (PowIndex.get N w r).leftGrade = a} = ![0, k, k] a) ↔
    (∀ h : Fin 2,
      Fintype.card {r : Fin N //
        (e (PowIndex.get N w r)).1 = h} = k) := by
  constructor
  · intro hw h
    fin_cases h
    · have ha := hw (2 : Fin 3)
      have htypes :
          {r : Fin N // (e (PowIndex.get N w r)).1 = 0} =
            {r : Fin N // (PowIndex.get N w r).leftGrade = 2} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using ha
    · have ha := hw (1 : Fin 3)
      have htypes :
          {r : Fin N // (e (PowIndex.get N w r)).1 = 1} =
            {r : Fin N // (PowIndex.get N w r).leftGrade = 1} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using ha
  · intro hw a
    fin_cases a
    · change Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = 0} = 0
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun r ↦ ?_⟩
      have hr := r.2
      rw [he] at hr
      generalize hb : (e (PowIndex.get N w r.1)).1 = b at hr
      fin_cases b <;> simp_all
    · have hh := hw (1 : Fin 2)
      have htypes :
          {r : Fin N // (PowIndex.get N w r).leftGrade = 1} =
            {r : Fin N // (e (PowIndex.get N w r)).1 = 1} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using hh
    · have hh := hw (0 : Fin 2)
      have htypes :
          {r : Fin N // (PowIndex.get N w r).leftGrade = 2} =
            {r : Fin N // (e (PowIndex.get N w r)).1 = 0} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using hh

theorem gradeOne_fiber_predicate_iff
    (e : LiftedCoarsePair.{u} 6 1 ≃ Fin 2 × Fin 6)
    (he : ∀ p, p.leftGrade = ![0, 1] (e p).1)
    (N k : ℕ) (w : PowIndex (LiftedCoarsePair.{u} 6 1) N) :
    (∀ a : Fin 3,
      Fintype.card {r : Fin N //
        (PowIndex.get N w r).leftGrade = a} = ![k, k, 0] a) ↔
    (∀ h : Fin 2,
      Fintype.card {r : Fin N //
        (e (PowIndex.get N w r)).1 = h} = k) := by
  constructor
  · intro hw h
    fin_cases h
    · have ha := hw (0 : Fin 3)
      have htypes :
          {r : Fin N // (e (PowIndex.get N w r)).1 = 0} =
            {r : Fin N // (PowIndex.get N w r).leftGrade = 0} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using ha
    · have ha := hw (1 : Fin 3)
      have htypes :
          {r : Fin N // (e (PowIndex.get N w r)).1 = 1} =
            {r : Fin N // (PowIndex.get N w r).leftGrade = 1} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using ha
  · intro hw a
    fin_cases a
    · have hh := hw (0 : Fin 2)
      have htypes :
          {r : Fin N // (PowIndex.get N w r).leftGrade = 0} =
            {r : Fin N // (e (PowIndex.get N w r)).1 = 0} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using hh
    · have hh := hw (1 : Fin 2)
      have htypes :
          {r : Fin N // (PowIndex.get N w r).leftGrade = 1} =
            {r : Fin N // (e (PowIndex.get N w r)).1 = 1} := by
        congr 1
        funext r
        apply propext
        rw [he]
        generalize hb : (e (PowIndex.get N w r)).1 = b
        fin_cases b <;> simp_all
      simpa [htypes] using hh
    · change Fintype.card {r : Fin N //
          (PowIndex.get N w r).leftGrade = 2} = 0
      apply Fintype.card_eq_zero_iff.mpr
      refine ⟨fun r ↦ ?_⟩
      have hr := r.2
      rw [he] at hr
      generalize hb : (e (PowIndex.get N w r.1)).1 = b at hr
      fin_cases b <;> simp_all

theorem gradeThree_prescribed_word_card
    (e : LiftedCoarsePair.{u} 6 3 ≃ Fin 2 × Fin 6)
    (he : ∀ p, p.leftGrade = ![2, 1] (e p).1)
    (N k : ℕ) :
    Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 3) N //
          ∀ a : Fin 3,
            Fintype.card {r : Fin N //
              (PowIndex.get N w r).leftGrade = a} = ![0, k, k] a} =
      Nat.card
          {g : Fin N → Fin 2 //
            ∀ h, Fintype.card {r : Fin N // g r = h} = k} *
        6 ^ N := by
  have htypes :
      {w : PowIndex (LiftedCoarsePair.{u} 6 3) N //
        ∀ a : Fin 3,
          Fintype.card {r : Fin N //
            (PowIndex.get N w r).leftGrade = a} = ![0, k, k] a} =
        {w : PowIndex (LiftedCoarsePair.{u} 6 3) N //
          ∀ h : Fin 2,
            Fintype.card {r : Fin N //
              (e (PowIndex.get N w r)).1 = h} = k} := by
    congr 1
    funext w
    exact propext (gradeThree_fiber_predicate_iff e he N k w)
  rw [htypes]
  simpa only using mme_prescribed_product_alphabet_word_card
    2 6 N (fun _ ↦ k) (fun p ↦ (e p).1) e (fun _ ↦ rfl)

theorem gradeOne_prescribed_word_card
    (e : LiftedCoarsePair.{u} 6 1 ≃ Fin 2 × Fin 6)
    (he : ∀ p, p.leftGrade = ![0, 1] (e p).1)
    (N k : ℕ) :
    Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 1) N //
          ∀ a : Fin 3,
            Fintype.card {r : Fin N //
              (PowIndex.get N w r).leftGrade = a} = ![k, k, 0] a} =
      Nat.card
          {g : Fin N → Fin 2 //
            ∀ h, Fintype.card {r : Fin N // g r = h} = k} *
        6 ^ N := by
  have htypes :
      {w : PowIndex (LiftedCoarsePair.{u} 6 1) N //
        ∀ a : Fin 3,
          Fintype.card {r : Fin N //
            (PowIndex.get N w r).leftGrade = a} = ![k, k, 0] a} =
        {w : PowIndex (LiftedCoarsePair.{u} 6 1) N //
          ∀ h : Fin 2,
            Fintype.card {r : Fin N //
              (e (PowIndex.get N w r)).1 = h} = k} := by
    congr 1
    funext w
    exact propext (gradeOne_fiber_predicate_iff e he N k w)
  rw [htypes]
  simpa only using mme_prescribed_product_alphabet_word_card
    2 6 N (fun _ ↦ k) (fun p ↦ (e p).1) e (fun _ ↦ rfl)

end MME.DWZBalancedRowsAllowedCard

/-- Exact available-word cardinality for the four balanced rectangular
Table-2 rows. -/
theorem solution
    (m : ℕ) (s : Fin 15) (hs : s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 7) :
    let k := MME.DWZTable2Counts.split s 1 * m
    let N := MME.DWZTable2Counts.component s * m
    Nat.card
        {w : PowIndex (LiftedCoarsePair.{u} 6 (MME.DWZSquare.shapeZ s)) N //
          componentWordAllowed s m w} =
      Nat.card
          {g : Fin N → Fin 2 //
            ∀ h, Fintype.card {r : Fin N // g r = h} = k} *
        6 ^ N := by
  rcases mme_dwz_q6_balanced_rectangular_product_coordinates with
    ⟨⟨e3, he3⟩, ⟨e1, he1⟩⟩
  rcases hs with rfl | rfl | rfl | rfl
  · unfold componentWordAllowed
    simp [MME.DWZTable2Counts.component, MME.DWZTable2Counts.split,
      MME.DWZSquare.shapeZ]
    have hsplit : ∀ a : Fin 3,
        ![0, 60557650000000, 60557650000000] a * m =
          ![0, 60557650000000 * m, 60557650000000 * m] a := by
      intro a
      fin_cases a <;> simp
    simpa [hsplit] using
      (MME.DWZBalancedRowsAllowedCard.gradeThree_prescribed_word_card e3 he3
        (121115300000000 * m) (60557650000000 * m))
  · unfold componentWordAllowed
    simp [MME.DWZTable2Counts.component, MME.DWZTable2Counts.split,
      MME.DWZSquare.shapeZ]
    have hsplit : ∀ a : Fin 3,
        ![66665900000000, 66665900000000, 0] a * m =
          ![66665900000000 * m, 66665900000000 * m, 0] a := by
      intro a
      fin_cases a <;> simp
    simpa [hsplit] using
      (MME.DWZBalancedRowsAllowedCard.gradeOne_prescribed_word_card e1 he1
        (133331800000000 * m) (66665900000000 * m))
  · unfold componentWordAllowed
    simp [MME.DWZTable2Counts.component, MME.DWZTable2Counts.split,
      MME.DWZSquare.shapeZ]
    have hsplit : ∀ a : Fin 3,
        ![0, 60557650000000, 60557650000000] a * m =
          ![0, 60557650000000 * m, 60557650000000 * m] a := by
      intro a
      fin_cases a <;> simp
    simpa [hsplit] using
      (MME.DWZBalancedRowsAllowedCard.gradeThree_prescribed_word_card e3 he3
        (121115300000000 * m) (60557650000000 * m))
  · unfold componentWordAllowed
    simp [MME.DWZTable2Counts.component, MME.DWZTable2Counts.split,
      MME.DWZSquare.shapeZ]
    have hsplit : ∀ a : Fin 3,
        ![66665900000000, 66665900000000, 0] a * m =
          ![66665900000000 * m, 66665900000000 * m, 0] a := by
      intro a
      fin_cases a <;> simp
    simpa [hsplit] using
      (MME.DWZBalancedRowsAllowedCard.gradeOne_prescribed_word_card e1 he1
        (133331800000000 * m) (66665900000000 * m))
