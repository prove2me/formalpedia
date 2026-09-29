-- Prove2me | solution 1 for mme_recursive_yz_child_plan_of_interior_joint_histograms
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T10:22:10.308723+00:00
-- url     : https://prove2.me/submissions/4ae69a2b-19eb-4679-9123-136a07992d06

import Theorems.Thm_mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
import Theorems.Thm_mme_recursive_yz_boundary_profile_of_grade_support

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical

/-- Stage mass identities make a supported integer coupling sufficient for child extraction. -/
theorem stage_child_matrix_extraction_of_joint_histogram
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D) (j : Fin A.childCells)
    (joint : (Fin 3 → CompleteWord A.ell) → ℕ)
    (hmarginal : ∀ i s, ∑ v, (if v i = s then joint v else 0) =
      A.mu i (A.childCell j) s)
    (hgrade : ∀ i s, 0 < A.mu i (A.childCell j) s →
      grade s = ((A.childCell j).2.val i).val)
    (hsupport : ∀ v, 0 < joint v →
      ∀ r, (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun i k ↦ ∑ v, joint v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
    Restrict (MMObj K (5 ^ n 0 2) (5 ^ n 0 1) (5 ^ n 1 2))
      (A.childTensor K j) := by
  classical
  have hm : ∑ v, joint v = A.childMultiplicity j := by
    have h := A.mass 0 (A.childCell j)
    simp_rw [← hmarginal 0] at h
    rw [Finset.sum_comm] at h
    simpa using h
  have hg (v : Fin 3 → CompleteWord A.ell) (hv : 0 < joint v) (i : Fin 3) :
      grade (v i) = ((A.childCell j).2.val i).val := by
    apply hgrade i (v i)
    rw [← hmarginal i (v i)]
    have hle := Finset.single_le_sum (fun w (_ : w ∈ Finset.univ) ↦
      Nat.zero_le (if w i = v i then joint w else 0)) (Finset.mem_univ v)
    exact hv.trans_le (by simpa using hle)
  have hex := mme_recursive_CW_unbroken_matrix_extraction_of_joint_histogram
    (K := K) (Equiv.refl (Fin (A.childMultiplicity j))) (fun _ ↦ Unit.unit)
    (fun _ i ↦ ((A.childCell j).2.val i).val) (fun i _ ↦ A.mu i (A.childCell j))
    (fun _ ↦ joint) (by intro c; simpa using hm)
    (fun i _ s ↦ hmarginal i s) (fun _ v hv ↦ hg v hv) (fun _ v hv ↦ hsupport v hv)
  simpa only [Fintype.sum_unique, Stage.childTensor] using hex

/-- Preserve exact boundary profiles and use integer couplings only for interior children. -/
theorem stage_child_plan_of_interior_joint_histograms
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D)
    (joint : Fin A.childCells → (Fin 3 → CompleteWord A.ell) → ℕ)
    (hgrade : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      grade s = ((A.childCell j).2.val i).val)
    (hmarginal : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ i s, ∑ v, (if v i = s then joint j v else 0) = A.mu i (A.childCell j) s)
    (hsupport : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ v, 0 < joint j v → ∀ r,
        (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun j i k ↦ ∑ v, joint j v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
    ∃ M : A.ChildPlan K, ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      M.a j = 5 ^ n j 0 2 ∧ M.b j = 5 ^ n j 0 1 ∧ M.c j = 5 ^ n j 1 2 := by
  classical
  dsimp only
  let n := fun j i k ↦ ∑ v, joint j v *
    (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
  have hex (j : Fin A.childCells) : ∃ a b c : ℕ,
      (A.BoundaryChild j a b c ∨
        ((∀ i, 0 < ((A.childCell j).2.val i).val) ∧
          Restrict (MMObj K a b c) (A.childTensor K j))) ∧
      ((∀ i, 0 < ((A.childCell j).2.val i).val) →
        a = 5 ^ n j 0 2 ∧ b = 5 ^ n j 0 1 ∧ c = 5 ^ n j 1 2) := by
    by_cases hi : ∀ i, 0 < ((A.childCell j).2.val i).val
    · exact ⟨_, _, _, Or.inr ⟨hi, stage_child_matrix_extraction_of_joint_histogram
        A j (joint j) (hmarginal j hi) (hgrade j) (hsupport j hi)⟩,
        fun _ ↦ ⟨rfl, rfl, rfl⟩⟩
    · have hz : ∃ z, ((A.childCell j).2.val z).val = 0 := by
        simpa only [not_forall, Nat.not_lt, Nat.le_zero] using hi
      obtain ⟨z, hz⟩ := hz
      obtain ⟨B, hshape, hmu⟩ := mme_recursive_yz_boundary_profile_of_grade_support
        A j z hz (hgrade j)
      exact ⟨B.a z, B.b z, B.c z,
        Or.inl ⟨z, B, hshape, hmu, rfl, rfl, rfl⟩, fun h ↦ (hi h).elim⟩
  choose a b c hc hd using hex
  exact ⟨⟨a, b, c, hc⟩, hd⟩


theorem solution
    {K : Type*} [Field K] {D : HashExtraction.HashData}
    (A : Stage D)
    (joint : Fin A.childCells → (Fin 3 → CompleteWord A.ell) → ℕ)
    (hgrade : ∀ j i s, 0 < A.mu i (A.childCell j) s →
      grade s = ((A.childCell j).2.val i).val)
    (hmarginal : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ i s, ∑ v, (if v i = s then joint j v else 0) = A.mu i (A.childCell j) s)
    (hsupport : ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      ∀ v, 0 < joint j v → ∀ r,
        (v 0 r).val + (v 1 r).val + (v 2 r).val = 2) :
    let n := fun j i k ↦ ∑ v, joint j v *
      (Finset.univ.filter (fun r ↦ (v i r).val = 1 ∧ (v k r).val = 1)).card
    ∃ M : A.ChildPlan K, ∀ j, (∀ i, 0 < ((A.childCell j).2.val i).val) →
      M.a j = 5 ^ n j 0 2 ∧ M.b j = 5 ^ n j 0 1 ∧ M.c j = 5 ^ n j 1 2 := by
  exact stage_child_plan_of_interior_joint_histograms A joint hgrade hmarginal hsupport
#print axioms solution
