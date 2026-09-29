-- Prove2me | solution 1 for mme_dwz_table2_useful_block_typical_and_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:15:16.871212+00:00
-- url     : https://prove2.me/submissions/816ec363-c177-4deb-9133-42a8abad3c86

import Definitions.Def_mme_dwz_table2_useful_block
import Theorems.Thm_mme_dwz_table2_useful_implies_compatible

open BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2UsefulBridge

private theorem fine_pair_eq_of_fst_and_coarse
    (x p : Fin 3 × Fin 3)
    (hfst : x.1 = p.1)
    (hcoarse : MME.DWZTable2Counts.coarseOf x =
      MME.DWZTable2Counts.coarseOf p) : x = p := by
  apply Prod.ext
  · exact hfst
  · apply Fin.ext
    have hsum := congrArg Fin.val hcoarse
    simp only [MME.DWZTable2Counts.coarseOf] at hsum
    have hfstval := congrArg Fin.val hfst
    omega

private def componentFiberEquiv
    {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15) (small : Position → Fin 3 × Fin 3)
    (p : Fin 3 × Fin 3) :
    (Σ s : Fin 15, {t : Position // outer t = s ∧ small t = p}) ≃
      {t : Position // small t = p} where
  toFun x := ⟨x.2.1, x.2.2.2⟩
  invFun t := ⟨outer t.1, ⟨t.1, rfl, t.2⟩⟩
  left_inv x := by
    rcases x with ⟨s, ⟨t, hs, hp⟩⟩
    cases hs
    rfl
  right_inv t := by cases t; rfl

private theorem useful_component_fine_fiber_card
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer)
    (s : Fin 15) (p : Fin 3 × Fin 3) :
    Fintype.card
        {t : Position // outer t = s ∧ small.1 t = p} =
      if MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s p.1 * m
      else 0 := by
  classical
  by_cases hs : MME.DWZSquare.shapeZ s =
      MME.DWZTable2Counts.coarseOf p
  · simp only [hs, if_true]
    let e :
        {t : Position // outer t = s ∧ small.1 t = p} ≃
          {t : Position // outer t = s ∧ (small.1 t).1 = p.1} :=
      Equiv.subtypeEquiv (Equiv.refl _) (by
        intro t
        constructor
        · intro h
          exact ⟨h.1, congrArg Prod.fst h.2⟩
        · intro h
          have hout : outer t = s := by simpa using h.1
          have hleft : (small.1 t).1 = p.1 := by simpa using h.2
          refine ⟨hout, fine_pair_eq_of_fst_and_coarse _ p hleft ?_⟩
          calc
            MME.DWZTable2Counts.coarseOf (small.1 t) =
                MME.DWZSquare.shapeZ (outer t) := small.2.1 t
            _ = MME.DWZSquare.shapeZ s := congrArg _ hout
            _ = MME.DWZTable2Counts.coarseOf p := hs)
    rw [Fintype.card_congr e]
    exact small.2.2 s p.1
  · simp only [hs, if_false]
    letI : IsEmpty {t : Position // outer t = s ∧ small.1 t = p} :=
      ⟨by
        intro t
        apply hs
        calc
          MME.DWZSquare.shapeZ s =
              MME.DWZSquare.shapeZ (outer t.1) :=
            (congrArg MME.DWZSquare.shapeZ t.2.1).symm
          _ = MME.DWZTable2Counts.coarseOf (small.1 t.1) :=
            (small.2.1 t.1).symm
          _ = MME.DWZTable2Counts.coarseOf p := congrArg _ t.2.2⟩
    exact Fintype.card_eq_zero

private theorem table2_component_splits_aggregate_gamma
    (p : Fin 3 × Fin 3) :
    (∑ s : Fin 15,
      if MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s p.1
      else 0) = MME.DWZTable2Counts.gamma p := by
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

end MME.DWZTable2UsefulBridge

open MME.DWZTable2UsefulBridge

theorem solution
    (m : ℕ) {Position : Type*} [Fintype Position]
    (outer : Position → Fin 15)
    (small : MME.DWZTable2StandardForm.UsefulBlock m outer) :
    (∀ p : Fin 3 × Fin 3,
      Fintype.card {t : Position // small.1 t = p} =
        MME.DWZTable2Counts.gamma p * m) ∧
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
      Fintype.card
          {t : Position //
            regionOfShape (outer t) = r ∧ (small.1 t).1 = a} =
        MME.DWZTable2Cardinality.cellCount m r a := by
  classical
  constructor
  · intro p
    rw [← Fintype.card_congr
        (MME.DWZTable2UsefulBridge.componentFiberEquiv outer small.1 p),
      Fintype.card_sigma]
    simp_rw [MME.DWZTable2UsefulBridge.useful_component_fine_fiber_card
      m outer small]
    calc
      (∑ s : Fin 15,
          if MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
            MME.DWZTable2Counts.split s p.1 * m
          else 0) =
          (∑ s : Fin 15,
            if MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
              MME.DWZTable2Counts.split s p.1
            else 0) * m := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro s hs
              split <;> simp_all
      _ = MME.DWZTable2Counts.gamma p * m := by
        rw [MME.DWZTable2UsefulBridge.table2_component_splits_aggregate_gamma]
  · exact mme_dwz_table2_useful_implies_compatible
      m outer small.1 small.2.2
