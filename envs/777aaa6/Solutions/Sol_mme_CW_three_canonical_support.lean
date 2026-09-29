-- Prove2me | solution 1 for mme_CW_three_canonical_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:31:25.466461+00:00
-- url     : https://prove2.me/submissions/dc1b5cd9-bb90-4c77-a165-c11182017b19

import Definitions.Def_mme_dwz_cw_square_fine_split_grading

open PiTensorProduct BigOperators Module

namespace MME.DWZStep1Support

open MME

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

private theorem basis_mem_grade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private theorem cwThreeCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 3) (i : Fin (q + 2)) :
    (cwThreeCanonicalGrading K q).blockProj s a
        (cwThreeCanonicalBasis K q s i) =
      if h : cwSquareCoordGrade q i = a then
        ⟨cwThreeCanonicalBasis K q s i, by
          simpa [h] using basis_mem_grade
            (cwThreeCanonicalBasis K q s) (cwSquareCoordGrade q) i⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwThreeCanonicalGrading K q) s (cwSquareCoordGrade q i) _
      (basis_mem_grade
        (cwThreeCanonicalBasis K q s) (cwSquareCoordGrade q) i)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwThreeCanonicalGrading K q) s a (cwSquareCoordGrade q i)
      (Ne.symm h) _
      (basis_mem_grade
        (cwThreeCanonicalBasis K q s) (cwSquareCoordGrade q) i)

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwThreeCanonicalBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin (q + 2)) :
    cwThreeCanonicalBasis K q s a = cwVec K q s a := by
  fin_cases s <;>
    exact Pi.basisFun_apply K (Fin (q + 2)) a

private def cwO (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩
private def cwM (q : ℕ) (i : Fin q) : Fin (q + 2) :=
  ⟨i.val + 1, by omega⟩
private def cwT (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

private def cwSupportedTriple (q : ℕ)
    (a b c : Fin (q + 2)) : Prop :=
  (∃ i : Fin q, a = cwO q ∧ b = cwM q i ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwO q ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwM q i ∧ c = cwO q) ∨
  (a = cwO q ∧ b = cwO q ∧ c = cwT q) ∨
  (a = cwO q ∧ b = cwT q ∧ c = cwO q) ∨
  (a = cwT q ∧ b = cwO q ∧ c = cwO q)

private theorem cwCoordGrade_O (q : ℕ) :
    cwSquareCoordGrade q (cwO q) = 0 := by
  simp [cwSquareCoordGrade, cwO]

private theorem cwCoordGrade_M (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwM q i) = 1 := by
  simp [cwSquareCoordGrade, cwM]
  omega

private theorem cwCoordGrade_T (q : ℕ) :
    cwSquareCoordGrade q (cwT q) = 2 := by
  simp [cwSquareCoordGrade, cwT]

private theorem cwSupportedTriple_grade_sum_two
    (q : ℕ) (a b c : Fin (q + 2))
    (h : cwSupportedTriple q a b c) :
    (cwSquareCoordGrade q a).val + (cwSquareCoordGrade q b).val +
      (cwSquareCoordGrade q c).val = 2 := by
  rcases h with
    ⟨i, rfl, rfl, rfl⟩ | ⟨i, rfl, rfl, rfl⟩ |
    ⟨i, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    simp [cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T]

private abbrev CWTerm (q : ℕ) := (Fin q × Fin 3) ⊕ Fin 3

private def cwTermTriple (q : ℕ) : CWTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (_i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (_i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (_i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwT q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwO q

private noncomputable def cwTermMonom
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    PiTensorProduct K (CWSpace K q) :=
  CWMonom K q (cwTermTriple q t 0) (cwTermTriple q t 1)
    (cwTermTriple q t 2)

private theorem cwTerm_supported (q : ℕ) (t : CWTerm q) :
    cwSupportedTriple q
      (cwTermTriple q t 0) (cwTermTriple q t 1)
      (cwTermTriple q t 2) := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwTermTriple, cwSupportedTriple]

private theorem CWTensor_eq_sum_terms
    (K : Type u) [Field K] (q : ℕ) :
    CWTensor K q = ∑ t : CWTerm q, cwTermMonom K q t := by
  have hM (i : Fin q) :
      (⟨i.val + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + i.val, by omega⟩ := by
    apply Fin.ext
    change i.val + 1 = 1 + i.val
    omega
  have hT :
      (⟨q + 1, by omega⟩ : Fin (q + 2)) =
        ⟨1 + q, by omega⟩ := by
    apply Fin.ext
    change q + 1 = 1 + q
    omega
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  unfold CWTensor cwTermMonom
  simp [cwTermTriple, Fin.sum_univ_succ, cwO, cwM, cwT, hM, hT]
  abel

private def cwTriple {α : Type*} (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

private theorem CWMonom_eq_tprod_cwVec
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    CWMonom K q a b c =
      tprod K (fun s => cwVec K q s (cwTriple a b c s)) := by
  unfold CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem cwTermMonom_eq_tprod_basis
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    cwTermMonom K q t =
      tprod K (fun s => cwThreeCanonicalBasis K q s
        (cwTermTriple q t s)) := by
  unfold cwTermMonom
  rw [CWMonom_eq_tprod_cwVec]
  congr 1
  funext s
  rw [cwThreeCanonicalBasis_apply]
  fin_cases s <;> rfl

private theorem cwThreeCanonical_map_basis_tprod_zero
    (K : Type u) [Field K] (q : ℕ)
    (σ : Fin 3 → Fin 3) (idx : Fin 3 → Fin (q + 2))
    (h : ∃ s, cwSquareCoordGrade q (idx s) ≠ σ s) :
    PiTensorProduct.map
        (fun s => (cwThreeCanonicalGrading K q).blockProj s (σ s))
        (tprod K (fun s => cwThreeCanonicalBasis K q s (idx s))) = 0 := by
  rcases h with ⟨s, hs⟩
  rw [PiTensorProduct.map_tprod]
  have hz :
      (cwThreeCanonicalGrading K q).blockProj s (σ s)
          (cwThreeCanonicalBasis K q s (idx s)) = 0 := by
    rw [cwThreeCanonical_blockProj_basis]
    simp [hs]
  exact (PiTensorProduct.tprod K).map_coord_zero s hz

private theorem cwThreeCanonical_term_zero
    (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 3)
    (t : CWTerm q)
    (hsum : (σ 0).val + (σ 1).val + (σ 2).val ≠ 2) :
    PiTensorProduct.map
        (fun s => (cwThreeCanonicalGrading K q).blockProj s (σ s))
        (cwTermMonom K q t) = 0 := by
  rw [cwTermMonom_eq_tprod_basis]
  apply cwThreeCanonical_map_basis_tprod_zero
  by_contra hnone
  push_neg at hnone
  have hgrade := cwSupportedTriple_grade_sum_two q
    (cwTermTriple q t 0) (cwTermTriple q t 1)
    (cwTermTriple q t 2) (cwTerm_supported q t)
  have h0 := congrArg Fin.val (hnone 0)
  have h1 := congrArg Fin.val (hnone 1)
  have h2 := congrArg Fin.val (hnone 2)
  simp only at h0 h1 h2
  exact hsum (by omega)

/-- Every nonzero block of the canonical three-grading of `CW_q` has total
grade two. This is the one-copy support law needed to reason about the two
level-one halves separately. -/
private theorem cwThreeCanonical_support_aux
    (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 3)
    (hsum : (σ 0).val + (σ 1).val + (σ 2).val ≠ 2) :
    (cwThreeCanonicalGrading K q).blockTensor σ = 0 := by
  change PiTensorProduct.map
      (fun s => (cwThreeCanonicalGrading K q).blockProj s (σ s))
      (CWTensor K q) = 0
  rw [CWTensor_eq_sum_terms]
  let F := PiTensorProduct.map
    (fun s => (cwThreeCanonicalGrading K q).blockProj s (σ s))
  change F (∑ t : CWTerm q, cwTermMonom K q t) = 0
  calc
    _ = ∑ t : CWTerm q, F (cwTermMonom K q t) :=
      map_sum F (cwTermMonom K q) Finset.univ
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t
      exact cwThreeCanonical_term_zero K q σ t hsum

end MME.DWZStep1Support

open MME.DWZStep1Support

theorem solution
    (K : Type*) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 3)
    (hsum : (sigma 0).val + (sigma 1).val + (sigma 2).val ≠ 2) :
    (cwThreeCanonicalGrading K q).blockTensor sigma = 0 := by
  exact cwThreeCanonical_support_aux K q sigma hsum
