-- Prove2me | solution 1 for mme_CW_fourth_literal_term_projection_zero_of_sum_ne_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:03:41.027786+00:00
-- url     : https://prove2.me/submissions/d3dcc41f-e47a-4049-9549-c38fd1f34372

import Definitions.Def_mme_CW_fourth_literal_support_words
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.Tactic

open MME TensorProduct PiTensorProduct BigOperators DirectSum Module

universe u

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace MME.StothersFourth

private abbrev FourthIndex (q : ℕ) : Type :=
  (Fin (q + 2) × Fin (q + 2)) × (Fin (q + 2) × Fin (q + 2))

private theorem basis_mem_cwBasisGrade
    {K : Type u} [Field K]
    {V : Type u} [AddCommGroup V] [Module K V]
    {ι κ : Type*} [DecidableEq κ]
    (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwLiteralTermMonomial_eq_tprod
    (K : Type u) [Field K] (q : ℕ) (t : CWLiteralTerm q) :
    cwLiteralTermMonomial K q t =
      PiTensorProduct.tprod K
        (fun s => cwVec K q s (cwLiteralTermTriple q t s)) := by
  unfold cwLiteralTermMonomial CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem cwSquareCanonicalBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) =
      cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2)))
      (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [cwVec, Pi.basisFun_apply]

private theorem cwFourthCanonicalBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (p : FourthIndex q) :
    cwFourthCanonicalBasis K q s p =
      cwSquareCanonicalBasis K q s p.1 ⊗ₜ[K]
        cwSquareCanonicalBasis K q s p.2 := by
  unfold cwFourthCanonicalBasis
  exact Module.Basis.tensorProduct_apply _ _ _ _

private theorem interchange_tprod
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (PiTensorProduct.tprod K v)
        (PiTensorProduct.tprod K w) =
      PiTensorProduct.tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (PiTensorProduct.tprod K v))
      (PiTensorProduct.tprod K w) = _
  rw [interchange]
  change (PiTensorProduct.lift interchangeOuter
      (PiTensorProduct.tprod K v)) (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v))
      (PiTensorProduct.tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem cwFourLiteralTerm_eq_basis_tprod
    (K : Type u) [Field K] (q : ℕ)
    (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    interchange
        (interchange (cwLiteralTermMonomial K q t₁)
          (cwLiteralTermMonomial K q t₂))
        (interchange (cwLiteralTermMonomial K q t₃)
          (cwLiteralTermMonomial K q t₄)) =
      PiTensorProduct.tprod K (fun s =>
        cwFourthCanonicalBasis K q s
          (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)) := by
  rw [cwLiteralTermMonomial_eq_tprod, cwLiteralTermMonomial_eq_tprod,
    cwLiteralTermMonomial_eq_tprod, cwLiteralTermMonomial_eq_tprod,
    interchange_tprod, interchange_tprod, interchange_tprod]
  congr 1
  funext s
  rw [cwFourthCanonicalBasis_apply,
    cwSquareCanonicalBasis_apply, cwSquareCanonicalBasis_apply]
  rfl

private theorem cwFourthCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin 9)
    (p : FourthIndex q) :
    (cwFourthCanonicalGrading K q).blockProj s a
        (cwFourthCanonicalBasis K q s p) =
      if h : cwFourthPairGrade q p = a then
        ⟨cwFourthCanonicalBasis K q s p, by
          simpa [h] using basis_mem_cwBasisGrade
            (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwFourthCanonicalGrading K q) s (cwFourthPairGrade q p) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwFourthCanonicalGrading K q) s a (cwFourthPairGrade q p)
      (Ne.symm h) _
      (basis_mem_cwBasisGrade
        (cwFourthCanonicalBasis K q s) (cwFourthPairGrade q) p)

private theorem sum_fin_three (f : Fin 3 → ℕ) :
    (∑ s, f s) = f 0 + f 1 + f 2 := by
  simp [Fin.sum_univ_succ, Nat.add_assoc]

private theorem cwSquareCoordGrade_zero (q : ℕ) :
    cwSquareCoordGrade q (cwZeroIndex q) = 0 := by
  simp [cwSquareCoordGrade, cwZeroIndex]

private theorem cwSquareCoordGrade_middle (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwMiddleIndex q i) = 1 := by
  have hi := i.isLt
  simp [cwSquareCoordGrade, cwMiddleIndex]
  omega

private theorem cwSquareCoordGrade_top (q : ℕ) :
    cwSquareCoordGrade q (cwTopIndex q) = 2 := by
  simp [cwSquareCoordGrade, cwTopIndex]

private theorem cwSquareCoordGrade_term_sum
    (q : ℕ) (t : CWLiteralTerm q) :
    (cwSquareCoordGrade q (cwLiteralTermTriple q t 0)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 1)).val +
      (cwSquareCoordGrade q (cwLiteralTermTriple q t 2)).val = 2 := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;>
    simp [cwLiteralTermTriple, cwSquareCoordGrade_zero,
      cwSquareCoordGrade_middle, cwSquareCoordGrade_top]

private theorem fourthIndex_grade_sum
    (q : ℕ) (t₁ t₂ t₃ t₄ : CWLiteralTerm q) :
    (cwFourthPairGrade q
      (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 0)).val +
    (cwFourthPairGrade q
      (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 1)).val +
    (cwFourthPairGrade q
      (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ 2)).val = 8 := by
  have h₁ := cwSquareCoordGrade_term_sum q t₁
  have h₂ := cwSquareCoordGrade_term_sum q t₂
  have h₃ := cwSquareCoordGrade_term_sum q t₃
  have h₄ := cwSquareCoordGrade_term_sum q t₄
  simp only [cwFourthPairGrade, cwSquarePairGrade,
    cwFourthIndexOfLiteralTerms]
  omega

end MME.StothersFourth

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- A literal fourth-power monomial projects to zero at every address whose
three grades do not have total degree eight. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) ≠ 8)
    (t₁ t₂ t₃ t₄ : MME.StothersFourth.CWLiteralTerm q) :
    PiTensorProduct.map
        (fun s => (MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
          s (sigma s))
        (MME.interchange
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₁)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₂))
          (MME.interchange
            (MME.StothersFourth.cwLiteralTermMonomial K q t₃)
            (MME.StothersFourth.cwLiteralTermMonomial K q t₄))) = 0 := by
  let F := PiTensorProduct.map
    (fun s => (MME.StothersFourth.cwFourthCanonicalGrading K q).blockProj
      s (sigma s))
  calc
    _ = F (PiTensorProduct.tprod K (fun s =>
          MME.StothersFourth.cwFourthCanonicalBasis K q s
            (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
              t₁ t₂ t₃ t₄ s))) := by
      exact congrArg F
        (MME.StothersFourth.cwFourLiteralTerm_eq_basis_tprod
          K q t₁ t₂ t₃ t₄)
    _ = 0 := by
      rw [PiTensorProduct.map_tprod]
      have hdiff : ∃ s : Fin 3,
          MME.StothersFourth.cwFourthPairGrade q
              (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
                t₁ t₂ t₃ t₄ s) ≠ sigma s := by
        by_contra hnone
        push_neg at hnone
        apply hsum
        have h0 := congrArg Fin.val (hnone 0)
        have h1 := congrArg Fin.val (hnone 1)
        have h2 := congrArg Fin.val (hnone 2)
        rw [MME.StothersFourth.sum_fin_three]
        have hgrade := MME.StothersFourth.fourthIndex_grade_sum
          q t₁ t₂ t₃ t₄
        omega
      obtain ⟨s, hs⟩ := hdiff
      apply (PiTensorProduct.tprod K).map_coord_zero s
      rw [MME.StothersFourth.cwFourthCanonical_blockProj_basis, dif_neg hs]
