-- Prove2me | solution 1 for mme_CW_fourth_block_nonzero_of_literal_terms
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:05:59.61883+00:00
-- url     : https://prove2.me/submissions/3af57120-15b6-4acb-9130-17294431612a

import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms
import Theorems.Thm_mme_CW_literal_term_triple_injective
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

private theorem linearMap_pair_fintype_sum
    {R I M N P : Type*} [Semiring R] [Fintype I]
    [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P]
    (A : N →ₗ[R] P) (B : M →ₗ[R] N) (f : I → M) :
    A (B (∑ i, f i)) = ∑ i, A (B (f i)) := by
  rw [map_sum B, map_sum A]

private theorem four_sum_eq_single
    {I₁ I₂ I₃ I₄ X : Type*}
    [Fintype I₁] [Fintype I₂] [Fintype I₃] [Fintype I₄]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq I₃] [DecidableEq I₄]
    [AddCommMonoid X] (w₁ : I₁) (w₂ : I₂) (w₃ : I₃) (w₄ : I₄)
    (x : X) :
    (∑ i₄, ∑ i₃, ∑ i₂, ∑ i₁,
      if i₁ = w₁ ∧ i₂ = w₂ ∧ i₃ = w₃ ∧ i₄ = w₄ then x else 0) = x := by
  calc
    _ = ∑ i₃, ∑ i₂, ∑ i₁,
        if i₁ = w₁ ∧ i₂ = w₂ ∧ i₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₄
      intro i₄ hi₄
      apply Fintype.sum_eq_zero
      intro i₃
      apply Fintype.sum_eq_zero
      intro i₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₄]
    _ = ∑ i₂, ∑ i₁,
        if i₁ = w₁ ∧ i₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₃
      intro i₃ hi₃
      apply Fintype.sum_eq_zero
      intro i₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₃]
    _ = ∑ i₁,
        if i₁ = w₁ ∧ w₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₂
      intro i₂ hi₂
      apply Fintype.sum_eq_zero
      intro i₁
      simp [hi₂]
    _ = if w₁ = w₁ ∧ w₂ = w₂ ∧ w₃ = w₃ ∧ w₄ = w₄ then x else 0 := by
      apply Fintype.sum_eq_single w₁
      intro i₁ hi₁
      simp [hi₁]
    _ = x := by simp

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

private theorem fourthIndexOfLiteralTerms_eq_iff
    (q : ℕ) (t₁ t₂ t₃ t₄ w₁ w₂ w₃ w₄ : CWLiteralTerm q) :
    (∀ s, cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s =
        cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄ s) ↔
      t₁ = w₁ ∧ t₂ = w₂ ∧ t₃ = w₃ ∧ t₄ = w₄ := by
  constructor
  · intro h
    have h₁ : cwLiteralTermTriple q t₁ = cwLiteralTermTriple q w₁ := by
      funext s
      exact congrArg (fun p : FourthIndex q => p.1.1) (h s)
    have h₂ : cwLiteralTermTriple q t₂ = cwLiteralTermTriple q w₂ := by
      funext s
      exact congrArg (fun p : FourthIndex q => p.1.2) (h s)
    have h₃ : cwLiteralTermTriple q t₃ = cwLiteralTermTriple q w₃ := by
      funext s
      exact congrArg (fun p : FourthIndex q => p.2.1) (h s)
    have h₄ : cwLiteralTermTriple q t₄ = cwLiteralTermTriple q w₄ := by
      funext s
      exact congrArg (fun p : FourthIndex q => p.2.2) (h s)
    exact ⟨mme_CW_literal_term_triple_injective q h₁,
      mme_CW_literal_term_triple_injective q h₂,
      mme_CW_literal_term_triple_injective q h₃,
      mme_CW_literal_term_triple_injective q h₄⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact fun _ => rfl

private noncomputable def fourthBasisSelector
    (K : Type u) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (selected : Fin 3 → FourthIndex q) (s : Fin 3) :
    (cwFourthCanonicalGrading K q).classOf s (sigma s) →ₗ[K] K :=
  ((cwFourthCanonicalBasis K q s).constr K
      (fun p => if p = selected s then 1 else 0)).comp
    ((cwFourthCanonicalGrading K q).decomp s (sigma s)).subtype

private theorem fourthBasisSelector_apply_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (selected : Fin 3 → FourthIndex q) (s : Fin 3) (p : FourthIndex q) :
    fourthBasisSelector K q sigma selected s
        ((cwFourthCanonicalGrading K q).blockProj s (sigma s)
          (cwFourthCanonicalBasis K q s p)) =
      if cwFourthPairGrade q p = sigma s then
        if p = selected s then 1 else 0
      else 0 := by
  rw [cwFourthCanonical_blockProj_basis]
  split_ifs with hgrade hselected
  · simp [fourthBasisSelector, hselected]
  · simp [fourthBasisSelector, hselected]
  · simp [fourthBasisSelector]

private noncomputable def scalarUnit
    (K : Type u) [Field K] :
    PiTensorProduct K (fun _ : Fin 3 => K) :=
  PiTensorProduct.tprod K (fun _ => (1 : K))

private theorem scalarUnit_ne_zero
    (K : Type u) [Field K] : scalarUnit K ≠ 0 := by
  let b : Basis ((s : Fin 3) → Unit) K
      (PiTensorProduct K (fun _ : Fin 3 => K)) :=
    Basis.piTensorProduct (fun _ : Fin 3 => Basis.singleton Unit K)
  have hbasis : b (fun _ => Unit.unit) = scalarUnit K := by
    rw [Basis.piTensorProduct_apply]
    simp [scalarUnit, Basis.singleton_apply]
  rw [← hbasis]
  exact b.ne_zero _

private theorem selected_four_term_image
    (K : Type u) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (w₁ w₂ w₃ w₄ t₁ t₂ t₃ t₄ : CWLiteralTerm q)
    (hselected : ∀ s,
      cwFourthPairGrade q
        (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄ s) = sigma s) :
    PiTensorProduct.map
        (fourthBasisSelector K q sigma
          (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄))
        (PiTensorProduct.map
          (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
          (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) =
      if t₁ = w₁ ∧ t₂ = w₂ ∧ t₃ = w₃ ∧ t₄ = w₄ then
        scalarUnit K
      else 0 := by
  let A := PiTensorProduct.map
    (fourthBasisSelector K q sigma
      (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
  calc
    _ = A (B (PiTensorProduct.tprod K (fun s =>
          cwFourthCanonicalBasis K q s
            (cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s)))) := by
      exact congrArg (fun x => A (B x))
        (cwFourLiteralTerm_eq_basis_tprod K q t₁ t₂ t₃ t₄)
    _ = _ := by
      dsimp only [A, B]
      rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
      by_cases hterms : t₁ = w₁ ∧ t₂ = w₂ ∧ t₃ = w₃ ∧ t₄ = w₄
      · rw [if_pos hterms]
        rcases hterms with ⟨rfl, rfl, rfl, rfl⟩
        unfold scalarUnit
        congr 1
        funext s
        rw [fourthBasisSelector_apply_blockProj_basis]
        simp [hselected s]
      · rw [if_neg hterms]
        have hindex : ¬ ∀ s,
            cwFourthIndexOfLiteralTerms q t₁ t₂ t₃ t₄ s =
              cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄ s := by
          exact fun h => hterms ((fourthIndexOfLiteralTerms_eq_iff q
            t₁ t₂ t₃ t₄ w₁ w₂ w₃ w₄).mp h)
        push_neg at hindex
        obtain ⟨s, hs⟩ := hindex
        apply (PiTensorProduct.tprod K).map_coord_zero s
        rw [fourthBasisSelector_apply_blockProj_basis]
        simp [hs]

private theorem selected_blockTensor_image_eq_scalarUnit
    (K : Type u) [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (w₁ w₂ w₃ w₄ : CWLiteralTerm q)
    (hselected : ∀ s,
      cwFourthPairGrade q
        (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄ s) = sigma s) :
    PiTensorProduct.map
        (fourthBasisSelector K q sigma
          (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄))
        ((cwFourthCanonicalGrading K q).blockTensor sigma) =
      scalarUnit K := by
  change PiTensorProduct.map
      (fourthBasisSelector K q sigma
        (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄))
      (PiTensorProduct.map
        (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
        (cwFourthObj K q).t) = scalarUnit K
  rw [mme_CW_fourth_tensor_eq_sum_literal_terms]
  let A := PiTensorProduct.map
      (fourthBasisSelector K q sigma
        (cwFourthIndexOfLiteralTerms q w₁ w₂ w₃ w₄))
  let B := PiTensorProduct.map
    (fun s => (cwFourthCanonicalGrading K q).blockProj s (sigma s))
  let f₄ := fun t₄ : CWLiteralTerm q =>
    ∑ t₃ : CWLiteralTerm q, ∑ t₂ : CWLiteralTerm q,
      ∑ t₁ : CWLiteralTerm q,
      interchange
        (interchange (cwLiteralTermMonomial K q t₁)
          (cwLiteralTermMonomial K q t₂))
        (interchange (cwLiteralTermMonomial K q t₃)
          (cwLiteralTermMonomial K q t₄))
  calc
    _ = ∑ t₄ : CWLiteralTerm q, A (B (f₄ t₄)) :=
      linearMap_pair_fintype_sum A B f₄
    _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
        A (B (∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
          interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) := by
      apply Finset.sum_congr rfl
      intro t₄ _
      exact linearMap_pair_fintype_sum A B _
    _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
        ∑ t₂ : CWLiteralTerm q, A (B (∑ t₁ : CWLiteralTerm q,
          interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) := by
      apply Finset.sum_congr rfl
      intro t₄ _
      apply Finset.sum_congr rfl
      intro t₃ _
      exact linearMap_pair_fintype_sum A B _
    _ = ∑ t₄ : CWLiteralTerm q, ∑ t₃ : CWLiteralTerm q,
        ∑ t₂ : CWLiteralTerm q, ∑ t₁ : CWLiteralTerm q,
          A (B (interchange
            (interchange (cwLiteralTermMonomial K q t₁)
              (cwLiteralTermMonomial K q t₂))
            (interchange (cwLiteralTermMonomial K q t₃)
              (cwLiteralTermMonomial K q t₄)))) := by
      apply Finset.sum_congr rfl
      intro t₄ _
      apply Finset.sum_congr rfl
      intro t₃ _
      apply Finset.sum_congr rfl
      intro t₂ _
      exact linearMap_pair_fintype_sum A B _
    _ = scalarUnit K := by
      dsimp only [A, B]
      simp_rw [selected_four_term_image K q sigma w₁ w₂ w₃ w₄
        _ _ _ _ hselected]
      exact four_sum_eq_single w₁ w₂ w₃ w₄ (scalarUnit K)

end MME.StothersFourth

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- A literal fourth-power word in a graded address certifies that the
corresponding block tensor is nonzero. -/
theorem solution
    {K : Type u} [Field K] (q : ℕ) (sigma : Fin 3 → Fin 9)
    (w₁ w₂ w₃ w₄ : MME.StothersFourth.CWLiteralTerm q)
    (hselected : ∀ s,
      MME.StothersFourth.cwFourthPairGrade q
        (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
          w₁ w₂ w₃ w₄ s) = sigma s) :
    (MME.StothersFourth.cwFourthCanonicalGrading K q).blockTensor sigma ≠ 0 := by
  intro hzero
  have hmap := congrArg
    (PiTensorProduct.map
      (MME.StothersFourth.fourthBasisSelector K q sigma
        (MME.StothersFourth.cwFourthIndexOfLiteralTerms q
          w₁ w₂ w₃ w₄))) hzero
  rw [MME.StothersFourth.selected_blockTensor_image_eq_scalarUnit
    K q sigma w₁ w₂ w₃ w₄ hselected, map_zero] at hmap
  exact MME.StothersFourth.scalarUnit_ne_zero K hmap
