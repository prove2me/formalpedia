-- Prove2me | solution 1 for mme_dwz_table2_split_assignments_embed_typical_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T14:17:15.727722+00:00
-- url     : https://prove2.me/submissions/ed8f55c6-5854-4f2c-b01e-3ae9e184b27d

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening
import Theorems.Thm_mme_dwz_table2_regional_splits_aggregate_gamma

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZTable2TypicalFineWord

private def rightLabel : Fin 5 → Fin 3 → Fin 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![0, 2, 1], ![0, 0, 2]]

private theorem rightLabel_eq_of_coarse (p : Fin 3 × Fin 3) (k : Fin 5)
    (h : MME.DWZTable2Counts.coarseOf p = k) :
    rightLabel k p.1 = p.2 := by
  subst k
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

private theorem positive_cell_has_right
    (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3) :
    0 < MME.DWZTable2Cardinality.cellCount 1 r a →
      ∃ b : Fin 3,
        MME.DWZTable2Counts.coarseOf (a, b) =
          MME.DWZTable2Cardinality.coarseDegree r := by
  fin_cases r <;> fin_cases a <;> decide

private theorem occupied_cell_positive_at_one
    (m : ℕ) (A : MME.DWZTable2Cardinality.SplitAssignments m)
    (r : MME.DWZTable2Cardinality.SplitRegion)
    (u : MME.DWZTable2Cardinality.RegionPosition m r) :
    0 < MME.DWZTable2Cardinality.cellCount 1 r ((A r).1 u) := by
  have hpos :
      0 < Fintype.card
        {v : MME.DWZTable2Cardinality.RegionPosition m r //
          (A r).1 v = (A r).1 u} :=
    Fintype.card_pos_iff.mpr ⟨⟨u, rfl⟩⟩
  rw [(A r).2] at hpos
  cases r <;>
    simpa [MME.DWZTable2Cardinality.cellCount] using
      Nat.pos_of_mul_pos_right hpos

private def assembleFineWord
    (m : ℕ) (A : MME.DWZTable2Cardinality.SplitAssignments m) :
    (Σ r : MME.DWZTable2Cardinality.SplitRegion,
      MME.DWZTable2Cardinality.RegionPosition m r) → Fin 3 × Fin 3 :=
  fun x =>
    let left := (A x.1).1 x.2
    (left,
      rightLabel (MME.DWZTable2Cardinality.coarseDegree x.1) left)

private theorem assembleFineWord_coarse
    (m : ℕ) (A : MME.DWZTable2Cardinality.SplitAssignments m)
    (x : Σ r : MME.DWZTable2Cardinality.SplitRegion,
      MME.DWZTable2Cardinality.RegionPosition m r) :
    MME.DWZTable2Counts.coarseOf (assembleFineWord m A x) =
      MME.DWZTable2Cardinality.coarseDegree x.1 := by
  have hpos := occupied_cell_positive_at_one m A x.1 x.2
  rcases positive_cell_has_right x.1 ((A x.1).1 x.2) hpos with ⟨b, hb⟩
  have hright := rightLabel_eq_of_coarse
    (((A x.1).1 x.2), b)
    (MME.DWZTable2Cardinality.coarseDegree x.1) hb
  simpa [assembleFineWord, hright] using hb

private def fineFiberSigmaEquiv
    (m : ℕ) (A : MME.DWZTable2Cardinality.SplitAssignments m)
    (p : Fin 3 × Fin 3) :
    {x : Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r //
      assembleFineWord m A x = p} ≃
      Σ r : MME.DWZTable2Cardinality.SplitRegion,
        {u : MME.DWZTable2Cardinality.RegionPosition m r //
          assembleFineWord m A ⟨r, u⟩ = p} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x with | mk r u => cases u; rfl

private theorem local_fine_fiber_card
    (m : ℕ) (A : MME.DWZTable2Cardinality.SplitAssignments m)
    (p : Fin 3 × Fin 3)
    (r : MME.DWZTable2Cardinality.SplitRegion) :
    Fintype.card
        {u : MME.DWZTable2Cardinality.RegionPosition m r //
          assembleFineWord m A ⟨r, u⟩ = p} =
      if MME.DWZTable2Cardinality.coarseDegree r =
          MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Cardinality.cellCount m r p.1
      else 0 := by
  classical
  by_cases hr : MME.DWZTable2Cardinality.coarseDegree r =
      MME.DWZTable2Counts.coarseOf p
  · simp only [hr, if_true]
    let e :
        {u : MME.DWZTable2Cardinality.RegionPosition m r //
          assembleFineWord m A ⟨r, u⟩ = p} ≃
          {u : MME.DWZTable2Cardinality.RegionPosition m r //
            (A r).1 u = p.1} :=
      Equiv.subtypeEquiv (Equiv.refl _) (by
        intro u
        constructor
        · intro h
          exact congrArg Prod.fst h
        · intro hleft
          have hleft' : (A r).1 u = p.1 := by simpa using hleft
          apply Prod.ext
          · exact hleft'
          · dsimp [assembleFineWord]
            rw [hleft']
            exact rightLabel_eq_of_coarse p
              (MME.DWZTable2Cardinality.coarseDegree r) hr.symm)
    rw [Fintype.card_congr e]
    exact (A r).2 p.1
  · simp only [hr, if_false]
    letI : IsEmpty
        {u : MME.DWZTable2Cardinality.RegionPosition m r //
          assembleFineWord m A ⟨r, u⟩ = p} :=
      ⟨by
        intro u
        apply hr
        calc
          MME.DWZTable2Cardinality.coarseDegree r =
              MME.DWZTable2Counts.coarseOf
                (assembleFineWord m A ⟨r, u.1⟩) :=
            (assembleFineWord_coarse m A ⟨r, u.1⟩).symm
          _ = MME.DWZTable2Counts.coarseOf p := congrArg _ u.2⟩
    exact Fintype.card_eq_zero

private theorem boundary_sum_scaled
    (m : ℕ) (p : Fin 3 × Fin 3) :
    (∑ s : MME.DWZTable2Cardinality.BoundaryShape,
      if MME.DWZSquare.shapeZ s.1 =
          MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s.1 p.1 * m
      else 0) =
      (∑ s : Fin 15,
        if (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
            MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
          MME.DWZTable2Counts.split s p.1
        else 0) * m := by
  classical
  let boundary : Fin 15 → Prop := fun s ↦
    MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0
  let f : Fin 15 → ℕ := fun s ↦
    if MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
      MME.DWZTable2Counts.split s p.1
    else 0
  calc
    (∑ s : MME.DWZTable2Cardinality.BoundaryShape,
      if MME.DWZSquare.shapeZ s.1 =
          MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s.1 p.1 * m
      else 0) =
        ∑ s : {s : Fin 15 // boundary s}, f s.1 * m := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hz : MME.DWZSquare.shapeZ s.1 =
            MME.DWZTable2Counts.coarseOf p <;> simp [f, hz]
    _ =
        (∑ s : {s : Fin 15 // boundary s}, f s.1) * m := by
          rw [Finset.sum_mul]
    _ = (∑ s ∈ Finset.univ.filter boundary, f s) * m := by
      congr 1
    _ = (∑ s : Fin 15, if boundary s then f s else 0) * m := by
      rw [Finset.sum_filter]
    _ = (∑ s : Fin 15,
        if (MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0) ∧
            MME.DWZSquare.shapeZ s = MME.DWZTable2Counts.coarseOf p then
          MME.DWZTable2Counts.split s p.1
        else 0) * m := by
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hb : MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 <;>
        by_cases hz : MME.DWZSquare.shapeZ s =
          MME.DWZTable2Counts.coarseOf p <;>
        simp [boundary, f, hb, hz]

private theorem scaled_region_cell_gamma
    (m : ℕ) (p : Fin 3 × Fin 3) :
    (∑ r : MME.DWZTable2Cardinality.SplitRegion,
      if MME.DWZTable2Cardinality.coarseDegree r =
          MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Cardinality.cellCount m r p.1
      else 0) = MME.DWZTable2Counts.gamma p * m := by
  rw [Fintype.sum_sum_type]
  simp only [MME.DWZTable2Cardinality.coarseDegree,
    MME.DWZTable2Cardinality.cellCount]
  rw [boundary_sum_scaled]
  rw [show
      (∑ k : Fin 5,
        if k = MME.DWZTable2Counts.coarseOf p then
          MME.DWZTable2Counts.plusSplit k p.1 * m
        else 0) =
      MME.DWZTable2Counts.plusSplit
        (MME.DWZTable2Counts.coarseOf p) p.1 * m by simp]
  rw [← Nat.add_mul,
    mme_dwz_table2_regional_splits_aggregate_gamma]

private abbrev TaggedPosition (m : ℕ) :=
  Σ r : MME.DWZTable2Cardinality.SplitRegion,
    MME.DWZTable2Cardinality.RegionPosition m r

private abbrev CoarseWord (m : ℕ) : TaggedPosition m → Fin 5 :=
  fun x ↦ MME.DWZTable2Cardinality.coarseDegree x.1

private abbrev TypicalFiber (m : ℕ) :=
  {small : TaggedPosition m → Fin 3 × Fin 3 //
    (∀ x, MME.DWZTable2Counts.coarseOf (small x) = CoarseWord m x) ∧
    ∀ p, Fintype.card {x // small x = p} =
      MME.DWZTable2Counts.gamma p * m}

private def assignmentToTypical (m : ℕ) :
    MME.DWZTable2Cardinality.SplitAssignments m → TypicalFiber m :=
  fun A ↦ ⟨assembleFineWord m A, assembleFineWord_coarse m A, fun p ↦ by
    rw [Fintype.card_congr (fineFiberSigmaEquiv m A p), Fintype.card_sigma]
    simp_rw [local_fine_fiber_card]
    exact scaled_region_cell_gamma m p⟩

private theorem assignmentToTypical_injective (m : ℕ) :
    Function.Injective (assignmentToTypical m) := by
  intro A B hAB
  funext r
  apply Subtype.ext
  funext u
  have hword := congrArg
    (fun C : TypicalFiber m ↦ C.1 ⟨r, u⟩) hAB
  exact congrArg Prod.fst hword

private def coarseFiberSigmaEquiv (m : ℕ) (k : Fin 5) :
    {x : TaggedPosition m // CoarseWord m x = k} ≃
      Σ r : {r : MME.DWZTable2Cardinality.SplitRegion //
        MME.DWZTable2Cardinality.coarseDegree r = k},
        MME.DWZTable2Cardinality.RegionPosition m r.1 where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by rcases x with ⟨⟨r, hr⟩, u⟩; rfl

private theorem regional_mass_pushforward (k : Fin 5) :
    (∑ r : {r : MME.DWZTable2Cardinality.SplitRegion //
        MME.DWZTable2Cardinality.coarseDegree r = k},
      MME.DWZTable2Cardinality.regionSize 1 r.1) =
      MME.DWZTable2Counts.alphaZ k := by
  fin_cases k <;> decide

private theorem coarseWord_fiber_card (m : ℕ) (k : Fin 5) :
    Fintype.card {x : TaggedPosition m // CoarseWord m x = k} =
      MME.DWZTable2Counts.alphaZ k * m := by
  classical
  rw [Fintype.card_congr (coarseFiberSigmaEquiv m k), Fintype.card_sigma]
  simp only [MME.DWZTable2Cardinality.RegionPosition, Fintype.card_fin]
  change (∑ r : {r : MME.DWZTable2Cardinality.SplitRegion //
    MME.DWZTable2Cardinality.coarseDegree r = k},
      MME.DWZTable2Cardinality.regionSize m r.1) = _
  calc
    (∑ r : {r : MME.DWZTable2Cardinality.SplitRegion //
        MME.DWZTable2Cardinality.coarseDegree r = k},
      MME.DWZTable2Cardinality.regionSize m r.1) =
        (∑ r : {r : MME.DWZTable2Cardinality.SplitRegion //
          MME.DWZTable2Cardinality.coarseDegree r = k},
          MME.DWZTable2Cardinality.regionSize 1 r.1) * m := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      cases r.1 <;> simp [MME.DWZTable2Cardinality.regionSize]
    _ = MME.DWZTable2Counts.alphaZ k * m := by
      rw [regional_mass_pushforward]

end MME.DWZTable2TypicalFineWord

open MME.DWZTable2TypicalFineWord

theorem solution
    (m : ℕ) :
    let TaggedPosition :=
      Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r
    let CoarseWord : TaggedPosition → Fin 5 := fun x ↦
      MME.DWZTable2Cardinality.coarseDegree x.1
    let TypicalFiber :=
      {small : TaggedPosition → Fin 3 × Fin 3 //
        (∀ x, MME.DWZTable2Counts.coarseOf (small x) = CoarseWord x) ∧
        ∀ p, Fintype.card {x // small x = p} =
          MME.DWZTable2Counts.gamma p * m}
    (∀ k, Fintype.card {x : TaggedPosition // CoarseWord x = k} =
      MME.DWZTable2Counts.alphaZ k * m) ∧
    ∃ encode : MME.DWZTable2Cardinality.SplitAssignments m → TypicalFiber,
      Function.Injective encode := by
  exact ⟨coarseWord_fiber_card m, assignmentToTypical m,
    assignmentToTypical_injective m⟩
