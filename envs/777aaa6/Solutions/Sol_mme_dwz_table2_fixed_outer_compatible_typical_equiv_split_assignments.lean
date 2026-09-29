-- Prove2me | solution 1 for mme_dwz_table2_fixed_outer_compatible_typical_equiv_split_assignments
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T19:08:03.615696+00:00
-- url     : https://prove2.me/submissions/6b185dc5-2358-4d87-96f5-05699778be25

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening
import Theorems.Thm_mme_dwz_table2_regional_splits_aggregate_gamma

open BigOperators Finset

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZFixedOuterRowIncidence

open MME.DWZTable2Cardinality

def regionOfShape (s : Fin 15) : SplitRegion :=
  if h : MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private theorem coarseDegree_regionOfShape (s : Fin 15) :
    coarseDegree (regionOfShape s) = MME.DWZSquare.shapeZ s := by
  simp only [regionOfShape]
  split <;> rfl

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
    (K : Position → Fin 5) (I : Outer m K)
    (small : Typical m K) : Prop :=
  ∀ (r : SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position //
          regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
      cellCount m r a

private abbrev TaggedPosition (m : ℕ) :=
  Σ r : SplitRegion, RegionPosition m r

/-! ## A region-preserving layout for the fixed component word -/

private theorem region_component_pushforward (r : SplitRegion) :
    (∑ s : {s : Fin 15 // regionOfShape s = r},
      MME.DWZTable2Counts.component s.1) = regionSize 1 r := by
  classical
  fin_cases r <;> decide

private def groupedShapeFiberEquiv
    {Position : Type*} (shapeWord : Position → Fin 15)
    (r : SplitRegion) :
    (Σ s : {s : Fin 15 // regionOfShape s = r},
      {t : Position // shapeWord t = s.1}) ≃
      {t : Position // regionOfShape (shapeWord t) = r} where
  toFun x := ⟨x.2.1, by rw [x.2.2, x.1.2]⟩
  invFun t := ⟨⟨shapeWord t.1, t.2⟩, ⟨t.1, rfl⟩⟩
  left_inv x := by
    rcases x with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    cases ht
    rfl
  right_inv t := by cases t; rfl

private theorem component_word_region_card
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m)
    (r : SplitRegion) :
    Fintype.card {t : Position // regionOfShape (shapeWord t) = r} =
      regionSize m r := by
  rw [← Fintype.card_congr (groupedShapeFiberEquiv shapeWord r),
    Fintype.card_sigma]
  simp_rw [hshape]
  rw [← Finset.sum_mul, region_component_pushforward]
  cases r <;> simp [regionSize]

private noncomputable def regionFiberEquiv
    {m : ℕ} {Position : Type*} [Fintype Position]
    (shapeWord : Position → Fin 15)
    (hshape : ∀ s,
      Fintype.card {t : Position // shapeWord t = s} =
        MME.DWZTable2Counts.component s * m)
    (r : SplitRegion) :
    RegionPosition m r ≃
      {t : Position // regionOfShape (shapeWord t) = r} :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin,
      component_word_region_card shapeWord hshape r])

private noncomputable def outerLayout
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K) :
    TaggedPosition m ≃ Position :=
  (Equiv.sigmaCongrRight (regionFiberEquiv I.1 I.2.2)).trans
    (Equiv.sigmaFiberEquiv (fun t ↦ regionOfShape (I.1 t)))

private theorem outerLayout_apply
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (x : TaggedPosition m) :
    outerLayout I x = (regionFiberEquiv I.1 I.2.2 x.1 x.2).1 := by
  rfl

private theorem outerLayout_region
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (x : TaggedPosition m) :
    regionOfShape (I.1 (outerLayout I x)) = x.1 := by
  rw [outerLayout_apply]
  exact (regionFiberEquiv I.1 I.2.2 x.1 x.2).2

private theorem outerLayout_coarse
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (x : TaggedPosition m) :
    K (outerLayout I x) = coarseDegree x.1 := by
  calc
    K (outerLayout I x) = MME.DWZSquare.shapeZ (I.1 (outerLayout I x)) :=
      (I.2.1 (outerLayout I x)).symm
    _ = coarseDegree (regionOfShape (I.1 (outerLayout I x))) :=
      (coarseDegree_regionOfShape _).symm
    _ = coarseDegree x.1 := by rw [outerLayout_region]

/-! ## The canonical fine word attached to regional split assignments -/

private def rightLabel : Fin 5 → Fin 3 → Fin 3 :=
  ![![0, 0, 0], ![1, 0, 0], ![2, 1, 0], ![0, 2, 1], ![0, 0, 2]]

private theorem rightLabel_eq_of_coarse (p : Fin 3 × Fin 3) (k : Fin 5)
    (h : MME.DWZTable2Counts.coarseOf p = k) :
    rightLabel k p.1 = p.2 := by
  subst k
  rcases p with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> decide

private theorem positive_cell_has_right
    (r : SplitRegion) (a : Fin 3) :
    0 < cellCount 1 r a →
      ∃ b : Fin 3,
        MME.DWZTable2Counts.coarseOf (a, b) = coarseDegree r := by
  fin_cases r <;> fin_cases a <;> decide

private theorem occupied_cell_positive_at_one
    (m : ℕ) (A : SplitAssignments m)
    (r : SplitRegion) (u : RegionPosition m r) :
    0 < cellCount 1 r ((A r).1 u) := by
  have hpos :
      0 < Fintype.card
        {v : RegionPosition m r // (A r).1 v = (A r).1 u} :=
    Fintype.card_pos_iff.mpr ⟨⟨u, rfl⟩⟩
  rw [(A r).2] at hpos
  cases r <;>
    simpa [cellCount] using Nat.pos_of_mul_pos_right hpos

private def assembleFineWord
    (m : ℕ) (A : SplitAssignments m) :
    TaggedPosition m → Fin 3 × Fin 3 := fun x ↦
  let left := (A x.1).1 x.2
  (left, rightLabel (coarseDegree x.1) left)

private theorem assembleFineWord_coarse
    (m : ℕ) (A : SplitAssignments m) (x : TaggedPosition m) :
    MME.DWZTable2Counts.coarseOf (assembleFineWord m A x) =
      coarseDegree x.1 := by
  have hpos := occupied_cell_positive_at_one m A x.1 x.2
  rcases positive_cell_has_right x.1 ((A x.1).1 x.2) hpos with ⟨b, hb⟩
  have hright := rightLabel_eq_of_coarse
    (((A x.1).1 x.2), b) (coarseDegree x.1) hb
  simpa [assembleFineWord, hright] using hb

private def fineFiberSigmaEquiv
    (m : ℕ) (A : SplitAssignments m) (p : Fin 3 × Fin 3) :
    {x : TaggedPosition m // assembleFineWord m A x = p} ≃
      Σ r : SplitRegion,
        {u : RegionPosition m r // assembleFineWord m A ⟨r, u⟩ = p} where
  toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
  invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x with | mk r u => cases u; rfl

private theorem local_fine_fiber_card
    (m : ℕ) (A : SplitAssignments m) (p : Fin 3 × Fin 3)
    (r : SplitRegion) :
    Fintype.card
        {u : RegionPosition m r // assembleFineWord m A ⟨r, u⟩ = p} =
      if coarseDegree r = MME.DWZTable2Counts.coarseOf p then
        cellCount m r p.1
      else 0 := by
  classical
  by_cases hr : coarseDegree r = MME.DWZTable2Counts.coarseOf p
  · simp only [hr, if_true]
    let e :
        {u : RegionPosition m r // assembleFineWord m A ⟨r, u⟩ = p} ≃
          {u : RegionPosition m r // (A r).1 u = p.1} :=
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
            exact rightLabel_eq_of_coarse p (coarseDegree r) hr.symm)
    rw [Fintype.card_congr e]
    exact (A r).2 p.1
  · simp only [hr, if_false]
    letI : IsEmpty
        {u : RegionPosition m r // assembleFineWord m A ⟨r, u⟩ = p} :=
      ⟨by
        intro u
        apply hr
        calc
          coarseDegree r =
              MME.DWZTable2Counts.coarseOf
                (assembleFineWord m A ⟨r, u.1⟩) :=
            (assembleFineWord_coarse m A ⟨r, u.1⟩).symm
          _ = MME.DWZTable2Counts.coarseOf p := congrArg _ u.2⟩
    exact Fintype.card_eq_zero

private theorem boundary_sum_scaled
    (m : ℕ) (p : Fin 3 × Fin 3) :
    (∑ s : BoundaryShape,
      if MME.DWZSquare.shapeZ s.1 = MME.DWZTable2Counts.coarseOf p then
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
    (∑ s : BoundaryShape,
      if MME.DWZSquare.shapeZ s.1 = MME.DWZTable2Counts.coarseOf p then
        MME.DWZTable2Counts.split s.1 p.1 * m
      else 0) =
        ∑ s : {s : Fin 15 // boundary s}, f s.1 * m := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hz : MME.DWZSquare.shapeZ s.1 =
            MME.DWZTable2Counts.coarseOf p <;> simp [f, hz]
    _ = (∑ s : {s : Fin 15 // boundary s}, f s.1) * m := by
      rw [Finset.sum_mul]
    _ = (∑ s ∈ Finset.univ.filter boundary, f s) * m := by congr 1
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
      by_cases hb : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 <;>
        by_cases hz : MME.DWZSquare.shapeZ s =
          MME.DWZTable2Counts.coarseOf p <;>
        simp [boundary, f, hb, hz]

private theorem scaled_region_cell_gamma
    (m : ℕ) (p : Fin 3 × Fin 3) :
    (∑ r : SplitRegion,
      if coarseDegree r = MME.DWZTable2Counts.coarseOf p then
        cellCount m r p.1
      else 0) = MME.DWZTable2Counts.gamma p * m := by
  rw [Fintype.sum_sum_type]
  simp only [coarseDegree, cellCount]
  rw [boundary_sum_scaled]
  rw [show
      (∑ k : Fin 5,
        if k = MME.DWZTable2Counts.coarseOf p then
          MME.DWZTable2Counts.plusSplit k p.1 * m
        else 0) =
      MME.DWZTable2Counts.plusSplit
        (MME.DWZTable2Counts.coarseOf p) p.1 * m by simp]
  rw [← Nat.add_mul, mme_dwz_table2_regional_splits_aggregate_gamma]

/-! ## The two inverse maps -/

private noncomputable def assignmentWord
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) : Position → Fin 3 × Fin 3 := fun t ↦
  assembleFineWord m A ((outerLayout I).symm t)

@[simp] private theorem assignmentWord_outerLayout
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) (x : TaggedPosition m) :
    assignmentWord I A (outerLayout I x) = assembleFineWord m A x := by
  simp only [assignmentWord, Equiv.symm_apply_apply]

private theorem assignmentWord_coarse
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) (t : Position) :
    MME.DWZTable2Counts.coarseOf (assignmentWord I A t) = K t := by
  let x := (outerLayout I).symm t
  calc
    MME.DWZTable2Counts.coarseOf (assignmentWord I A t) =
        coarseDegree x.1 := assembleFineWord_coarse m A x
    _ = K (outerLayout I x) := (outerLayout_coarse I x).symm
    _ = K t := by simp [x]

private theorem assignmentWord_fine_card
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) (p : Fin 3 × Fin 3) :
    Fintype.card {t : Position // assignmentWord I A t = p} =
      MME.DWZTable2Counts.gamma p * m := by
  let e :
      {t : Position // assignmentWord I A t = p} ≃
        {x : TaggedPosition m // assembleFineWord m A x = p} :=
    Equiv.subtypeEquiv (outerLayout I).symm (by
      intro t
      rfl)
  rw [Fintype.card_congr e,
    Fintype.card_congr (fineFiberSigmaEquiv m A p), Fintype.card_sigma]
  simp_rw [local_fine_fiber_card]
  exact scaled_region_cell_gamma m p

private noncomputable def assignmentToTypical
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) : Typical m K :=
  ⟨assignmentWord I A, assignmentWord_coarse I A,
    assignmentWord_fine_card I A⟩

private theorem assignmentToTypical_compatible
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) :
    Compatible m K I (assignmentToTypical I A) := by
  classical
  intro r a
  let nestedEquiv :
      {u : RegionPosition m r // (A r).1 u = a} ≃
        {t : {t : Position // regionOfShape (I.1 t) = r} //
          ((assignmentToTypical I A).1 t.1).1 = a} :=
    Equiv.subtypeEquiv (regionFiberEquiv I.1 I.2.2 r) (by
      intro u
      change (A r).1 u = a ↔
        (assignmentWord I A
          (regionFiberEquiv I.1 I.2.2 r u).1).1 = a
      rw [← outerLayout_apply I ⟨r, u⟩,
        assignmentWord_outerLayout]
      rfl)
  let flattenEquiv :
      {t : {t : Position // regionOfShape (I.1 t) = r} //
          ((assignmentToTypical I A).1 t.1).1 = a} ≃
        {t : Position //
          regionOfShape (I.1 t) = r ∧
            ((assignmentToTypical I A).1 t).1 = a} :=
    Equiv.subtypeSubtypeEquivSubtypeInter
      (fun t : Position ↦ regionOfShape (I.1 t) = r)
      (fun t : Position ↦ ((assignmentToTypical I A).1 t).1 = a)
  rw [← Fintype.card_congr (nestedEquiv.trans flattenEquiv)]
  exact (A r).2 a

private noncomputable def assignmentToCompatible
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K) :
    SplitAssignments m → {small : Typical m K // Compatible m K I small} :=
  fun A ↦ ⟨assignmentToTypical I A, assignmentToTypical_compatible I A⟩

private noncomputable def compatibleToAssignment
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K) :
    {small : Typical m K // Compatible m K I small} → SplitAssignments m :=
  fun small r ↦ ⟨
    fun u ↦ (small.1.1 (outerLayout I ⟨r, u⟩)).1,
    fun a ↦ by
      classical
      let nestedEquiv :
          {u : RegionPosition m r //
              (small.1.1 (outerLayout I ⟨r, u⟩)).1 = a} ≃
            {t : {t : Position // regionOfShape (I.1 t) = r} //
              (small.1.1 t.1).1 = a} :=
        Equiv.subtypeEquiv (regionFiberEquiv I.1 I.2.2 r) (by
          intro u
          rw [← outerLayout_apply I ⟨r, u⟩])
      let flattenEquiv :
          {t : {t : Position // regionOfShape (I.1 t) = r} //
              (small.1.1 t.1).1 = a} ≃
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1.1 t).1 = a} :=
        Equiv.subtypeSubtypeEquivSubtypeInter
          (fun t : Position ↦ regionOfShape (I.1 t) = r)
          (fun t : Position ↦ (small.1.1 t).1 = a)
      rw [Fintype.card_congr (nestedEquiv.trans flattenEquiv)]
      exact small.2 r a⟩

private theorem compatibleToAssignment_assignmentToCompatible
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (A : SplitAssignments m) :
    compatibleToAssignment I (assignmentToCompatible I A) = A := by
  funext r
  apply Subtype.ext
  funext u
  change (assignmentWord I A (outerLayout I ⟨r, u⟩)).1 = (A r).1 u
  rw [assignmentWord_outerLayout]
  rfl

private theorem assignmentToCompatible_compatibleToAssignment
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K)
    (small : {small : Typical m K // Compatible m K I small}) :
    assignmentToCompatible I (compatibleToAssignment I small) = small := by
  apply Subtype.ext
  apply Subtype.ext
  funext t
  let x := (outerLayout I).symm t
  have ht : outerLayout I x = t := by simp [x]
  have hcoarse :
      MME.DWZTable2Counts.coarseOf (small.1.1 t) = coarseDegree x.1 := by
    calc
      MME.DWZTable2Counts.coarseOf (small.1.1 t) = K t := small.1.2.1 t
      _ = K (outerLayout I x) := by simp [x]
      _ = coarseDegree x.1 := outerLayout_coarse I x
  change assignmentWord I (compatibleToAssignment I small) t = small.1.1 t
  rw [← ht, assignmentWord_outerLayout]
  apply Prod.ext
  · rfl
  · change rightLabel (coarseDegree x.1) (small.1.1 (outerLayout I x)).1 =
      (small.1.1 (outerLayout I x)).2
    apply rightLabel_eq_of_coarse
    simpa only [ht] using hcoarse

noncomputable def compatibleTypicalEquivSplitAssignments
    {m : ℕ} {Position : Type*} [Fintype Position]
    {K : Position → Fin 5} (I : Outer m K) :
    {small : Typical m K // Compatible m K I small} ≃ SplitAssignments m where
  toFun := compatibleToAssignment I
  invFun := assignmentToCompatible I
  left_inv := assignmentToCompatible_compatibleToAssignment I
  right_inv := compatibleToAssignment_assignmentToCompatible I

end MME.DWZFixedOuterRowIncidence

open MME.DWZFixedOuterRowIncidence

theorem solution
    (m : ℕ)
    {Position : Type*} [Fintype Position]
    (K : Position → Fin 5)
    (I : {w : Position → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t : Position // w t = s} =
        MME.DWZTable2Counts.component s * m}) :
    let regionOfShape :
        Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
      if h : MME.DWZSquare.shapeX s = 0 ∨
          MME.DWZSquare.shapeY s = 0 then
        Sum.inl ⟨s, h⟩
      else
        Sum.inr (MME.DWZSquare.shapeZ s)
    let Typical :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    let Compatible : Typical → Prop := fun small ↦
      ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
        Fintype.card
            {t : Position //
              regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
          MME.DWZTable2Cardinality.cellCount m r a
    Nonempty
      ({small : Typical // Compatible small} ≃
        MME.DWZTable2Cardinality.SplitAssignments m) := by
  classical
  exact ⟨compatibleTypicalEquivSplitAssignments I⟩
