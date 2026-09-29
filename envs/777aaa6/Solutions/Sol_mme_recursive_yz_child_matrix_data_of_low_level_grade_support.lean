-- Prove2me | solution 1 for mme_recursive_yz_child_matrix_data_of_low_level_grade_support
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:01:20.455773+00:00
-- url     : https://prove2.me/submissions/23f872e0-564c-4f9c-aa68-9461f3c37b2d

import Definitions.Def_mme_recursive_yz_boundary_child_plan
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.Boundary

private theorem word_grade_zero {ell : ℕ} (s : CompleteWord ell)
    (h : CWCells.grade s = 0) : s = fun _ ↦ 0 := by
  funext r
  apply Fin.ext
  have hh : ∀ r, (s r).val = 0 := by
    simpa [CWCells.grade] using (Finset.sum_eq_zero_iff_of_nonneg
      (fun r (_ : r ∈ (Finset.univ : Finset (Fin (2 ^ (ell - 1))))) ↦ Nat.zero_le (s r).val)).mp h
  exact hh r

private theorem zero_profile {ell L : ℕ} (mu : CompleteWord ell → ℕ)
    (hmass : ∑ s, mu s = L)
    (hgrade : ∀ s, 0 < mu s → CWCells.grade s = 0) :
    mu = fun s ↦ if s = (fun _ ↦ 0) then L else 0 := by
  classical
  have hs (s : CompleteWord ell) (h : s ≠ fun _ ↦ 0) : mu s = 0 := by
    by_contra hn
    exact h (word_grade_zero s (hgrade s (Nat.pos_of_ne_zero hn)))
  have hz : mu (fun _ ↦ 0) = L := by
    calc
      mu (fun _ ↦ 0) = ∑ s, mu s := (Finset.sum_eq_single (fun _ ↦ 0)
        (fun s _ h ↦ hs s h) (by simp)).symm
      _ = L := hmass
  funext s
  by_cases h : s = fun _ ↦ 0
  · simp [h, hz]
  · simp [h, hs s h]

private theorem flipLabel_eq_rev {ell : ℕ} (s : CompleteWord ell) :
    flipLabel s = fun r ↦ Fin.rev (s r) := by
  funext r
  apply Fin.ext
  simp [flipLabel, Fin.rev]

/-- Grade support and the stored boundary identities determine an exact boundary profile. -/
theorem stage_boundary_profile_of_grade_support
    {D : HashExtraction.HashData} (A : Stage D) (j : Fin A.childCells)
    (z : Fin 3) (hz : ((A.childCell j).2.val z).val = 0)
    (hg : ∀ i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ B : Boundary.Profile A.ell (A.childMultiplicity j),
      (∀ i, ((A.childCell j).2.val i).val = B.shape z i) ∧
      (∀ i, A.mu i (A.childCell j) = B.mu z i) := by
  classical
  let cell := A.childCell j
  have hm (i : Fin 3) : ∑ s, A.mu i cell s = A.childMultiplicity j := A.mass i cell
  have ht := cell.2.property.1.trans A.half_eq
  have hb (i : Fin 3) : (cell.2.val i).val ≤ 2 * 2 ^ (A.ell - 1) := by
    have h := (cell.2.val i).isLt
    rw [← A.half_eq]
    omega
  have hzero : A.mu z cell = fun s ↦ if s = (fun _ ↦ 0) then A.childMultiplicity j else 0 :=
    zero_profile _ (hm z) (fun s hs ↦ (hg z s hs).trans hz)
  have hrevs (s : CompleteWord A.ell) :
      flipLabel (flipLabel s) = s := by
    funext r
    apply Fin.ext
    simp only [flipLabel]
    have := (s r).isLt
    omega
  fin_cases z
  · let B : Boundary.Profile A.ell (A.childMultiplicity j) :=
      ⟨(cell.2.val 1).val, hb 1, A.mu 1 cell, hm 1,
        fun s hs ↦ hg 1 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · exact hz
      · rfl
      · change (cell.2.val 2).val = 2 * 2 ^ (A.ell - 1) - (cell.2.val 1).val
        change (cell.2.val 0).val = 0 at hz
        omega
    · intro i
      fin_cases i
      · exact hzero
      · rfl
      · funext s
        change A.mu 2 cell s = A.mu 1 cell (flipLabel s)
        rw [flipLabel_eq_rev]
        exact A.boundary.2.1 cell hz s
  · let B : Boundary.Profile A.ell (A.childMultiplicity j) :=
      ⟨(cell.2.val 2).val, hb 2, A.mu 2 cell, hm 2,
        fun s hs ↦ hg 2 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · change (cell.2.val 0).val = 2 * 2 ^ (A.ell - 1) - (cell.2.val 2).val
        change (cell.2.val 1).val = 0 at hz
        omega
      · exact hz
      · rfl
    · intro i
      fin_cases i
      · funext s
        change A.mu 0 cell s = A.mu 2 cell (flipLabel s)
        rw [A.boundary.2.2 cell hz, ← flipLabel_eq_rev, hrevs]
      · exact hzero
      · rfl
  · let B : Boundary.Profile A.ell (A.childMultiplicity j) :=
      ⟨(cell.2.val 0).val, hb 0, A.mu 0 cell, hm 0,
        fun s hs ↦ hg 0 s (Nat.pos_of_ne_zero hs)⟩
    refine ⟨B, ?_, ?_⟩
    · intro i
      fin_cases i
      · rfl
      · change (cell.2.val 1).val = 2 * 2 ^ (A.ell - 1) - (cell.2.val 0).val
        change (cell.2.val 2).val = 0 at hz
        omega
      · exact hz
    · intro i
      fin_cases i
      · rfl
      · funext s
        change A.mu 1 cell s = A.mu 0 cell (flipLabel s)
        rw [flipLabel_eq_rev]
        exact A.boundary.1 cell hz s
      · exact hzero

/-- A grade-supported boundary child has an exact matrix extraction without a map hypothesis. -/
theorem stage_boundary_matrix_extraction_of_grade_support
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (j : Fin A.childCells)
    (z : Fin 3) (hz : ((A.childCell j).2.val z).val = 0)
    (hg : ∀ i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ B : Boundary.Profile A.ell (A.childMultiplicity j),
      A.BoundaryChild j (B.a z) (B.b z) (B.c z) ∧
      Restrict (MMObj K (B.a z) (B.b z) (B.c z)) (A.childTensor K j) := by
  obtain ⟨B, hshape, hmu⟩ := stage_boundary_profile_of_grade_support A j z hz hg
  refine ⟨B, ⟨z, B, hshape, hmu, rfl, rfl, rfl⟩, ?_⟩
  have heq : A.childTensor K j = B.tensor K z := by
    simp only [Stage.childTensor, Profile.tensor, hshape, hmu]
  rw [heq]
  exact mme_recursive_yz_boundary_actual_matrix_extraction B z

/-- At the lowest recursive level every child is on the boundary, so scalar profiles suffice. -/
theorem stage_child_matrix_data_of_low_level_grade_support
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (hlevel : A.ell ≤ 1)
    (hg : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ M : A.ChildMM K, ∀ j, A.BoundaryChild j (M.a j) (M.b j) (M.c j) := by
  classical
  have hzero (j : Fin A.childCells) :
      ∃ z : Fin 3, ((A.childCell j).2.val z).val = 0 := by
    have ht := (A.childCell j).2.property.1.trans A.half_eq
    simp only [Nat.sub_eq_zero_of_le hlevel, pow_zero, mul_one] at ht
    by_contra hn
    push_neg at hn
    have h0 := hn 0
    have h1 := hn 1
    have h2 := hn 2
    omega
  choose z hz using hzero
  have hex (j : Fin A.childCells) :=
    stage_boundary_matrix_extraction_of_grade_support (K := K) A j (z j) (hz j) (hg j)
  choose B hb he using hex
  exact ⟨⟨fun j ↦ (B j).a (z j), fun j ↦ (B j).b (z j),
    fun j ↦ (B j).c (z j), he⟩, hb⟩


theorem solution
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (hlevel : A.ell ≤ 1)
    (hg : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      CWCells.grade s = ((A.childCell j).2.val i).val) :
    ∃ M : A.ChildMM K, ∀ j, A.BoundaryChild j (M.a j) (M.b j) (M.c j) := by
  exact stage_child_matrix_data_of_low_level_grade_support A hlevel hg
#print axioms solution
