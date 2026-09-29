-- Prove2me | solution 1 for mme_dwz_table2_exact_outer_profile_usefulBlock_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T11:33:20.515592+00:00
-- url     : https://prove2.me/submissions/be067862-811d-491e-b085-b51fed2cf80d

import Definitions.Def_mme_dwz_table2_useful_block
import Theorems.Thm_mme_dwz_table2_integer_counts_exact
import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_nonempty

open BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (m : ℕ) {Position : Type*}
    [Fintype Position] [DecidableEq Position]
    (outer : Position → Fin 15)
    (hProfile : ∀ s : Fin 15,
      Fintype.card {t : Position // outer t = s} =
        MME.DWZTable2Counts.component s * m) :
    Nonempty (MME.DWZTable2StandardForm.UsefulBlock m outer) := by
  classical
  have hRight (s : Fin 15) (a : Fin 3) :
      0 < MME.DWZTable2Counts.split s a →
        ∃ b : Fin 3,
          MME.DWZTable2Counts.coarseOf (a, b) =
            MME.DWZSquare.shapeZ s := by
    fin_cases s <;> fin_cases a <;> decide
  rcases mme_dwz_table2_integer_counts_exact with
    ⟨_, _, hSplitSum, _, _, _, _, _, _, _, _⟩
  have hLocalSum (s : Fin 15) :
      (∑ a : Fin 3, MME.DWZTable2Counts.split s a * m) =
        Fintype.card {t : Position // outer t = s} := by
    calc
      (∑ a : Fin 3, MME.DWZTable2Counts.split s a * m) =
          (∑ a : Fin 3, MME.DWZTable2Counts.split s a) * m := by
            rw [Finset.sum_mul]
      _ = MME.DWZTable2Counts.component s * m := by rw [hSplitSum s]
      _ = Fintype.card {t : Position // outer t = s} := (hProfile s).symm
  have hGlobalSum (s : Fin 15) :
      (∑ b : {b : Fin 15 × Fin 3 // b.1 = s},
        MME.DWZTable2Counts.split b.1.1 b.1.2 * m) =
        Fintype.card {t : Position // outer t = s} := by
    let e : {b : Fin 15 × Fin 3 // b.1 = s} ≃ Fin 3 :=
      { toFun := fun b ↦ b.1.2
        invFun := fun a ↦ ⟨(s, a), rfl⟩
        left_inv := fun b ↦ by
          apply Subtype.ext
          apply Prod.ext
          · exact b.2.symm
          · rfl
        right_inv := fun a ↦ rfl }
    calc
      (∑ b : {b : Fin 15 × Fin 3 // b.1 = s},
          MME.DWZTable2Counts.split b.1.1 b.1.2 * m) =
          ∑ a : Fin 3, MME.DWZTable2Counts.split s a * m := by
            apply Fintype.sum_equiv e
            intro b
            change MME.DWZTable2Counts.split b.1.1 b.1.2 * m =
              MME.DWZTable2Counts.split s b.1.2 * m
            rw [b.2]
      _ = Fintype.card {t : Position // outer t = s} := hLocalSum s
  obtain ⟨⟨fine, hFineCoarse, hFineFibers⟩⟩ :=
    mme_fintype_constrained_prescribed_fiber_function_nonempty
      outer Prod.fst
        (fun b : Fin 15 × Fin 3 ↦
          MME.DWZTable2Counts.split b.1 b.2 * m)
        hGlobalSum
  let left : Position → Fin 3 := fun t ↦ (fine t).2
  have hLeft (s : Fin 15) (a : Fin 3) :
      Fintype.card {t : Position // outer t = s ∧ left t = a} =
        MME.DWZTable2Counts.split s a * m := by
    let e : {t : Position // outer t = s ∧ left t = a} ≃
        {t : Position // fine t = (s, a)} :=
      Equiv.subtypeEquiv (Equiv.refl Position) (by
        intro t
        constructor
        · intro ht
          apply Prod.ext
          · exact (hFineCoarse t).trans ht.1
          · exact ht.2
        · intro ht
          have hfst := congrArg Prod.fst ht
          have hsnd := congrArg Prod.snd ht
          exact ⟨(hFineCoarse t).symm.trans hfst, hsnd⟩)
    rw [Fintype.card_congr e]
    exact hFineFibers (s, a)
  have hCellPositive (t : Position) :
      0 < MME.DWZTable2Counts.split (outer t) (left t) := by
    have hOccupied :
        0 < Fintype.card
          {u : Position // outer u = outer t ∧ left u = left t} :=
      Fintype.card_pos_iff.mpr ⟨⟨t, rfl, rfl⟩⟩
    rw [hLeft] at hOccupied
    exact Nat.pos_of_mul_pos_right hOccupied
  let right : Position → Fin 3 := fun t ↦
    Classical.choose (hRight (outer t) (left t) (hCellPositive t))
  let small : Position → Fin 3 × Fin 3 := fun t ↦ (left t, right t)
  refine ⟨⟨small, ?_, ?_⟩⟩
  · intro t
    exact Classical.choose_spec
      (hRight (outer t) (left t) (hCellPositive t))
  · intro s a
    simpa only [small] using hLeft s a
