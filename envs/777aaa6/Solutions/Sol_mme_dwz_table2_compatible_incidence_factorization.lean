-- Prove2me | solution 1 for mme_dwz_table2_compatible_incidence_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:21:13.842415+00:00
-- url     : https://prove2.me/submissions/c19b7310-870a-47cb-b4bf-9a608d7def59

import Theorems.Thm_mme_dwz_table2_fixed_small_compatible_outer_card_eq
import Theorems.Thm_mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2IncidenceIdentity

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
  if h : MME.DWZSquare.shapeX s = 0 ∨
      MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private abbrev Outer
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {w : Position → Fin 15 //
    (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
    ∀ s, Fintype.card {t : Position // w t = s} =
      MME.DWZTable2Counts.component s * m}

private abbrev Typical
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :=
  {small : Position → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
    ∀ p, Fintype.card {t : Position // small t = p} =
      MME.DWZTable2Counts.gamma p * m}

private def Compatible
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (I : Outer m K) (small : Typical m K) : Prop :=
  ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position //
          regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
      MME.DWZTable2Cardinality.cellCount m r a

private def swapIncidence
    (m : ℕ) {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) :
    (Σ small : Typical m K,
        {I : Outer m K // Compatible m K I small}) ≃
      (Σ I : Outer m K,
        {small : Typical m K // Compatible m K I small}) where
  toFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, z.2.2⟩⟩
  left_inv z := by
    rcases z with ⟨small, I, h⟩
    rfl
  right_inv z := by
    rcases z with ⟨I, small, h⟩
    rfl

private theorem compatible_outer_card_eq
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5) (small₁ small₂ : Typical m K) :
    Nat.card {I : Outer m K // Compatible m K I small₁} =
      Nat.card {I : Outer m K // Compatible m K I small₂} := by
  exact mme_dwz_table2_fixed_small_compatible_outer_card_eq
    m K small₁ small₂

private theorem compatible_typical_card_eq_split_assignments
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (K : Position → Fin 5) (I : Outer m K) :
    Nat.card {small : Typical m K // Compatible m K I small} =
      Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) := by
  apply Nat.card_congr
  exact Classical.choice
    (mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments
      m K I)

end MME.DWZTable2IncidenceIdentity

open MME.DWZTable2IncidenceIdentity

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Outer :=
      {w : Position → Fin 15 //
        (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
        ∀ s, Fintype.card {t : Position // w t = s} =
          MME.DWZTable2Counts.component s * m}
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Outer → Typical → Prop := fun I small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    ∀ small₀ : Typical,
      Nat.card Typical *
          Nat.card {I : Outer // Compatible I small₀} =
        Nat.card Outer *
          Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) := by
  classical
  change ∀ small₀ : Typical m K,
    Nat.card (Typical m K) *
        Nat.card {I : Outer m K // Compatible m K I small₀} =
      Nat.card (Outer m K) *
        Nat.card (MME.DWZTable2Cardinality.SplitAssignments m)
  intro small₀
  calc
    Nat.card (Typical m K) *
          Nat.card {I : Outer m K // Compatible m K I small₀} =
        Nat.card
          (Σ small : Typical m K,
            {I : Outer m K // Compatible m K I small}) := by
      rw [Nat.card_sigma]
      simp_rw [compatible_outer_card_eq m K _ small₀]
      simp
    _ = Nat.card
          (Σ I : Outer m K,
            {small : Typical m K // Compatible m K I small}) := by
      exact Nat.card_congr (swapIncidence m K)
    _ = Nat.card (Outer m K) *
          Nat.card (MME.DWZTable2Cardinality.SplitAssignments m) := by
      rw [Nat.card_sigma]
      simp_rw [compatible_typical_card_eq_split_assignments m K]
      simp
