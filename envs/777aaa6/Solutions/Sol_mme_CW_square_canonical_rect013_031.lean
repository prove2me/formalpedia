-- Prove2me | solution 1 for mme_CW_square_canonical_rect013_031
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:33:22.875093+00:00
-- url     : https://prove2.me/submissions/4f9f79ca-c8fd-4e2c-aea5-b426ead25f3d

import Definitions.Def_mme_CW_square_five_grade_certificate
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_permutation
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

open PiTensorProduct TensorProduct BigOperators DirectSum Module

namespace MME

universe u

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace TensorObj.TypeGrading

variable {K : Type u} [Field K] {d t : ℕ} {T : TensorObj K d}

lemma blockProj_apply_mem
    (G : T.TypeGrading t) (i : Fin d) (a : Fin t)
    (x : T.V i) (hx : x ∈ G.decomp i a) :
    G.blockProj i a x = ⟨x, hx⟩ := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  apply Subtype.ext
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact congrArg Subtype.val
    ((G.is_internal i).ofBijective_coeLinearMap_of_mem hx)

lemma blockProj_apply_mem_ne
    (G : T.TypeGrading t) (i : Fin d) (a b : Fin t) (hab : a ≠ b)
    (x : T.V i) (hx : x ∈ G.decomp i b) :
    G.blockProj i a x = 0 := by
  unfold TensorObj.TypeGrading.blockProj TensorObj.TypeGrading.modeLequiv
  simp only [LinearMap.comp_apply]
  rw [← DirectSum.apply_eq_component]
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne hab.symm hx

end TensorObj.TypeGrading

section BasisGrading

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V]
variable {ι κ : Type*} [DecidableEq κ]

def basisGrade (b : Basis ι K V) (g : ι → κ) (a : κ) : Submodule K V :=
  Submodule.span K (b '' {i | g i = a})

theorem basisGrade_isInternal (b : Basis ι K V) (g : ι → κ) :
    DirectSum.IsInternal (basisGrade b g) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro a
    simp_rw [basisGrade]
    rw [← Submodule.span_iUnion₂]
    rw [← Set.image_iUnion₂]
    apply b.linearIndependent.disjoint_span_image
    rw [Set.disjoint_left]
    intro i hi hi'
    simp only [Set.mem_setOf_eq] at hi
    rcases Set.mem_iUnion.mp hi' with ⟨c, hi'⟩
    rcases Set.mem_iUnion.mp hi' with ⟨hc, hi'⟩
    exact hc (hi'.symm.trans hi)
  · apply top_unique
    rw [← b.span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    exact le_iSup (basisGrade b g) (g i) <|
      Submodule.subset_span ⟨i, rfl, rfl⟩

theorem basis_mem_basisGrade (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ basisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

end BasisGrading

section CWSquareCanonical

/- The grading itself is imported from the shared canonical-grading module. -/
/-

private def cwSquareCoordGrade (q : ℕ) (a : Fin (q + 2)) : Fin 3 :=
  if a.val = 0 then 0 else if a.val = q + 1 then 2 else 1

private def cwSquarePairGrade (q : ℕ) (ab : Fin (q + 2) × Fin (q + 2)) : Fin 5 :=
  ⟨(cwSquareCoordGrade q ab.1).val + (cwSquareCoordGrade q ab.2).val, by omega⟩

private noncomputable def cwSquareCanonicalBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    Basis (Fin (q + 2) × Fin (q + 2)) K
      ((TensorObj.kron (CWObj K q) (CWObj K q)).V s) := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  exact match s with
    | ⟨0, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨1, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))
    | ⟨2, _⟩ => Module.Basis.tensorProduct (R := K) (S := K)
        (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))

private noncomputable def cwSquareCanonicalGrading
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.kron (CWObj K q) (CWObj K q)).TypeGrading 5 where
  decomp s := basisGrade (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q)
  is_internal s := basisGrade_isInternal (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q)
-/

private theorem cwSquareCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 5) (i j : Fin (q + 2)) :
    (cwSquareCanonicalGrading K q).blockProj s a
        (cwSquareCanonicalBasis K q s (i, j)) =
      if h : cwSquarePairGrade q (i, j) = a then
        ⟨cwSquareCanonicalBasis K q s (i, j), by
          simpa [h] using
            basis_mem_basisGrade (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j)⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K q) s (cwSquarePairGrade q (i, j)) _
      (basis_mem_basisGrade (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j))
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K q) s a (cwSquarePairGrade q (i, j)) (Ne.symm h) _
      (basis_mem_basisGrade (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j))

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwSquareBasis_apply
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a b : Fin (q + 2)) :
    cwSquareCanonicalBasis K q s (a, b) = cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
  letI : IsScalarTower K K (Fin (q + 2) → K) :=
    IsScalarTower.of_algebraMap_smul (by simp)
  fin_cases s <;>
    change (Module.Basis.tensorProduct (R := K) (S := K)
      (Pi.basisFun K (Fin (q + 2))) (Pi.basisFun K (Fin (q + 2)))) (a, b) = _ <;>
    rw [Module.Basis.tensorProduct_apply] <;>
    simp [cwVec, Pi.basisFun_apply]

private theorem interchange_tprod
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  rw [interchange]
  change (PiTensorProduct.lift interchangeOuter (tprod K v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem interchange_add_right
    {K : Type u} [Field K] {d : ℕ}
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (y z : PiTensorProduct K W) :
    interchange x (y + z) = interchange x y + interchange x z := by
  exact (interchange x).map_add y z

private theorem interchange_sum_right
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (x : PiTensorProduct K V) (f : ι → PiTensorProduct K W) :
    interchange x (∑ i, f i) = ∑ i, interchange x (f i) := by
  exact map_sum (interchange x) f Finset.univ

private theorem interchange_sum_left
    {K : Type u} [Field K] {d : ℕ} {ι : Type*} [Fintype ι]
    {V W : Fin d → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ι → PiTensorProduct K V) (y : PiTensorProduct K W) :
    interchange (∑ i, f i) y = ∑ i, interchange (f i) y := by
  have h :
      (interchange (∑ i, f i) :
        PiTensorProduct K W →ₗ[K]
          PiTensorProduct K (fun i => V i ⊗[K] W i)) =
        ∑ i, interchange (f i) :=
    map_sum interchange f Finset.univ
  simpa using congrArg (fun g => g y) h

private def cwO (q : ℕ) : Fin (q + 2) := ⟨0, by omega⟩
private def cwM (q : ℕ) (i : Fin q) : Fin (q + 2) := ⟨i.val + 1, by omega⟩
private def cwT (q : ℕ) : Fin (q + 2) := ⟨q + 1, by omega⟩

private def cwSupportedTriple (q : ℕ)
    (a b c : Fin (q + 2)) : Prop :=
  (∃ i : Fin q, a = cwO q ∧ b = cwM q i ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwO q ∧ c = cwM q i) ∨
  (∃ i : Fin q, a = cwM q i ∧ b = cwM q i ∧ c = cwO q) ∨
  (a = cwO q ∧ b = cwO q ∧ c = cwT q) ∨
  (a = cwO q ∧ b = cwT q ∧ c = cwO q) ∨
  (a = cwT q ∧ b = cwO q ∧ c = cwO q)

private theorem cwCoordGrade_O (q : ℕ) : cwSquareCoordGrade q (cwO q) = 0 := by
  simp [cwSquareCoordGrade, cwO]

private theorem cwCoordGrade_M (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwM q i) = 1 := by
  simp [cwSquareCoordGrade, cwM]
  omega

private theorem cwCoordGrade_T (q : ℕ) : cwSquareCoordGrade q (cwT q) = 2 := by
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
  | Sum.inl (i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
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
  CWMonom K q (cwTermTriple q t 0) (cwTermTriple q t 1) (cwTermTriple q t 2)

private theorem cwTerm_supported (q : ℕ) (t : CWTerm q) :
    cwSupportedTriple q
      (cwTermTriple q t 0) (cwTermTriple q t 1) (cwTermTriple q t 2) := by
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
  simp [cwTermTriple, Fin.sum_univ_succ, cwO, cwM, cwT,
    hM, hT]
  abel

private def cwTriple {α : Type*} (a b c : α) : Fin 3 → α
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c

/- Term-to-pure-tensor expansion is inlined at its only coupled use. -/
/-
noncomputable def cwSquare121_CWMonom_eq_tprod_cwVec
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    CWMonom K q a b c =
      tprod K (fun s => cwVec K q s (cwTriple a b c s)) := by
  unfold CWMonom
  congr 1
  funext s
  fin_cases s <;> rfl

-/

/-
noncomputable def cwSquare121_termMonom_eq_tprod_cwVec
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    cwTermMonom K q t =
      tprod K (fun s => cwVec K q s (cwTermTriple q t s)) := by
  unfold cwTermMonom
  rw [cwSquare121_CWMonom_eq_tprod_cwVec]
  congr 1
  funext s
  fin_cases s <;> rfl

-/

/- Support-zero is supplied by the elementary child. -/
/-
private theorem cwSquareCanonical_map_basis_tprod_zero
    (K : Type u) [Field K] (q : ℕ)
    (σ : Fin 3 → Fin 5) (idx : Fin 3 → Fin (q + 2) × Fin (q + 2))
    (h : ∃ s, cwSquarePairGrade q (idx s) ≠ σ s) :
    PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (tprod K (fun s => cwSquareCanonicalBasis K q s (idx s))) = 0 := by
  rcases h with ⟨s, hs⟩
  rw [PiTensorProduct.map_tprod]
  have hz :
      (cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareCanonicalBasis K q s (idx s)) = 0 := by
    exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K q) s (σ s) (cwSquarePairGrade q (idx s)) hs.symm _
      (basis_mem_basisGrade (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (idx s))
  exact (PiTensorProduct.tprod K).map_coord_zero s hz

noncomputable def cwSquare121_monom_pair_zero
    (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 5)
    (a₁ b₁ c₁ a₂ b₂ c₂ : Fin (q + 2))
    (h₁ : cwSupportedTriple q a₁ b₁ c₁)
    (h₂ : cwSupportedTriple q a₂ b₂ c₂)
    (hsum : (σ 0).val + (σ 1).val + (σ 2).val ≠ 4) :
    PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (CWMonom K q a₁ b₁ c₁)
          (CWMonom K q a₂ b₂ c₂)) = 0 := by
  have hmonom (a b c : Fin (q + 2)) :
      CWMonom K q a b c =
        tprod K (fun s => cwVec K q s (cwTriple a b c s)) := by
    unfold CWMonom
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hmonom a₁ b₁ c₁, hmonom a₂ b₂ c₂]
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTriple a₁ b₁ c₁ s)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTriple a₂ b₂ c₂ s)
  change PiTensorProduct.map
      (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
      (interchange (tprod K v₁) (tprod K v₂)) = 0
  have hpure :
      tprod K (fun s => v₁ s ⊗ₜ[K] v₂ s) =
        tprod K (fun s => cwSquareCanonicalBasis K q s
          (cwTriple a₁ b₁ c₁ s, cwTriple a₂ b₂ c₂ s)) := by
    congr 1
    funext s
    dsimp [v₁, v₂]
    rw [cwSquareBasis_apply]
  calc
    _ = PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (tprod K (fun s => v₁ s ⊗ₜ[K] v₂ s)) :=
      congrArg _ (interchange_tprod (K := K) v₁ v₂)
    _ = 0 := by
      refine (congrArg
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))) hpure).trans ?_
      apply cwSquareCanonical_map_basis_tprod_zero
      by_contra hnone
      push_neg at hnone
      have hgrade₁ := cwSupportedTriple_grade_sum_two q a₁ b₁ c₁ h₁
      have hgrade₂ := cwSupportedTriple_grade_sum_two q a₂ b₂ c₂ h₂
      have h0 := congrArg Fin.val (hnone 0)
      have h1 := congrArg Fin.val (hnone 1)
      have h2 := congrArg Fin.val (hnone 2)
      simp only [cwSquarePairGrade, cwTriple] at h0 h1 h2
      omega

private theorem cwSquareCanonical_support
    (K : Type u) [Field K] (q : ℕ) (I J L : Fin 5)
    (hsum : I.val + J.val + L.val ≠ 4) :
    (cwSquareCanonicalGrading K q).blockTensor (cwSquareBlockType I J L) = 0 := by
  change PiTensorProduct.map
      (fun s => (cwSquareCanonicalGrading K q).blockProj s
        (cwSquareBlockType I J L s))
      (interchange (CWTensor K q) (CWTensor K q)) = 0
  have hzero (a₁ b₁ c₁ a₂ b₂ c₂ : Fin (q + 2))
      (h₁ : cwSupportedTriple q a₁ b₁ c₁)
      (h₂ : cwSupportedTriple q a₂ b₂ c₂) :
      PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s
            (cwSquareBlockType I J L s))
          (interchange (CWMonom K q a₁ b₁ c₁)
            (CWMonom K q a₂ b₂ c₂)) = 0 := by
    apply cwSquare121_monom_pair_zero K q _ _ _ _ _ _ _ h₁ h₂
    simpa [cwSquareBlockType] using hsum
  rw [CWTensor_eq_sum_terms]
  let F := PiTensorProduct.map
    (fun s => (cwSquareCanonicalGrading K q).blockProj s
      (cwSquareBlockType I J L s))
  have hinter :
      interchange (∑ t : CWTerm q, cwTermMonom K q t)
          (∑ u : CWTerm q, cwTermMonom K q u) =
        ∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u) := by
    calc
      _ = ∑ t : CWTerm q,
          interchange (cwTermMonom K q t)
            (∑ u : CWTerm q, cwTermMonom K q u) :=
        interchange_sum_left (cwTermMonom K q)
          (∑ u : CWTerm q, cwTermMonom K q u)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact interchange_sum_right (cwTermMonom K q t) (cwTermMonom K q)
  change F
      (interchange (∑ t : CWTerm q, cwTermMonom K q t)
        (∑ u : CWTerm q, cwTermMonom K q u)) = 0
  calc
    _ = F (∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
      congrArg F hinter
    _ = ∑ t : CWTerm q, ∑ u : CWTerm q,
          F (interchange (cwTermMonom K q t) (cwTermMonom K q u)) := by
      calc
        _ = ∑ t : CWTerm q,
            F (∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
          map_sum F
            (fun t : CWTerm q => ∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          exact map_sum F
            (fun u : CWTerm q =>
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ
    _ = 0 := by
      apply Fintype.sum_eq_zero
      intro t
      apply Fintype.sum_eq_zero
      intro u
      apply hzero
      · exact cwTerm_supported q t
      · exact cwTerm_supported q u

-/

private theorem cwSquareCanonical_blockTensor_eq_term_pairs
    (K : Type u) [Field K] (q : ℕ) (σ : Fin 3 → Fin 5) :
    (cwSquareCanonicalGrading K q).blockTensor σ =
      ∑ t : CWTerm q, ∑ u : CWTerm q,
        PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u)) := by
  change PiTensorProduct.map
      (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
      (interchange (CWTensor K q) (CWTensor K q)) = _
  rw [CWTensor_eq_sum_terms]
  let F := PiTensorProduct.map
    (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
  have hinter :
      interchange (∑ t : CWTerm q, cwTermMonom K q t)
          (∑ u : CWTerm q, cwTermMonom K q u) =
        ∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u) := by
    calc
      _ = ∑ t : CWTerm q,
          interchange (cwTermMonom K q t)
            (∑ u : CWTerm q, cwTermMonom K q u) :=
        interchange_sum_left (cwTermMonom K q)
          (∑ u : CWTerm q, cwTermMonom K q u)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro t ht
        exact interchange_sum_right (cwTermMonom K q t) (cwTermMonom K q)
  change F
      (interchange (∑ t : CWTerm q, cwTermMonom K q t)
        (∑ u : CWTerm q, cwTermMonom K q u)) = _
  calc
    _ = F (∑ t : CWTerm q, ∑ u : CWTerm q,
          interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
      congrArg F hinter
    _ = _ := by
      calc
        _ = ∑ t : CWTerm q,
            F (∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) :=
          map_sum F
            (fun t : CWTerm q => ∑ u : CWTerm q,
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ
        _ = _ := by
          apply Finset.sum_congr rfl
          intro t ht
          exact map_sum F
            (fun u : CWTerm q =>
              interchange (cwTermMonom K q t) (cwTermMonom K q u)) Finset.univ

/- Scalar-selector API is needed only by the elementary child. -/
/-
private noncomputable def cwSquareSelectorMap
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (selected : ∀ s : Fin 3, Fin (q + 2) × Fin (q + 2))
    (output : ∀ s : Fin 3, (MMObj K n m p).V s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K]
      (MMObj K n m p).V s :=
  ((cwSquareCanonicalBasis K q s).constr K
      (fun idx => if idx = selected s then output s else 0)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareSelectorMap_apply_blockProj_basis
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (selected : ∀ s : Fin 3, Fin (q + 2) × Fin (q + 2))
    (output : ∀ s : Fin 3, (MMObj K n m p).V s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareSelectorMap K q n m p σ selected output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareCanonicalBasis K q s idx)) =
      if cwSquarePairGrade q idx = σ s then
        if idx = selected s then output s else 0
      else 0 := by
  rw [cwSquareCanonical_blockProj_basis]
  split_ifs with hgrade hsel
  · simp [cwSquareSelectorMap, Module.Basis.constr_basis, hsel]
  · simp [cwSquareSelectorMap, Module.Basis.constr_basis, hsel]
  · simp [cwSquareSelectorMap]

private theorem cwSquareSelectorMap_term_pair
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (selected : ∀ s : Fin 3, Fin (q + 2) × Fin (q + 2))
    (output : ∀ s : Fin 3, (MMObj K n m p).V s)
    (t u : CWTerm q) :
    PiTensorProduct.map
        (cwSquareSelectorMap K q n m p σ selected output)
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      tprod K (fun s =>
        if cwSquarePairGrade q
            (cwTermTriple q t s, cwTermTriple q u s) = σ s then
          if (cwTermTriple q t s, cwTermTriple q u s) = selected s then
            output s
          else 0
        else 0) := by
  have hterm (r : CWTerm q) :
      cwTermMonom K q r =
        tprod K (fun s => cwVec K q s (cwTermTriple q r s)) := by
    unfold cwTermMonom CWMonom
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hterm t, hterm u]
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q t s)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q u s)
  change PiTensorProduct.map
      (cwSquareSelectorMap K q n m p σ selected output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (tprod K v₁) (tprod K v₂))) = _
  have hinter := interchange_tprod (K := K) v₁ v₂
  refine (congrArg
    (fun z => PiTensorProduct.map
      (cwSquareSelectorMap K q n m p σ selected output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s)) z)) hinter).trans ?_
  have hinner :
      PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (tprod K (fun i => v₁ i ⊗ₜ[K] v₂ i)) =
        tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s)) :=
    PiTensorProduct.map_tprod _ _
  calc
    _ = PiTensorProduct.map
        (cwSquareSelectorMap K q n m p σ selected output)
        (tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      congrArg _ hinner
    _ = tprod K (fun s =>
        cwSquareSelectorMap K q n m p σ selected output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      PiTensorProduct.map_tprod _ _
    _ = _ := by
      congr 1
      funext s
      dsimp [v₁, v₂]
      have hbasis := (cwSquareBasis_apply K q s
        (cwTermTriple q t s) (cwTermTriple q u s)).symm
      refine (congrArg
        (fun z => cwSquareSelectorMap K q n m p σ selected output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s) z)) hbasis).trans ?_
      exact cwSquareSelectorMap_apply_blockProj_basis
        K q n m p σ selected output s _

/- Elementary scalar, rectangular, and central block calculations belong to
their independent child theorem. -/
private def cwScalarOutput
    (K : Type u) [Field K] : ∀ s : Fin 3, (MMObj K 1 1 1).V s
  | ⟨0, _⟩ => Pi.single (0, 0) 1
  | ⟨1, _⟩ => Pi.single (0, 0) 1
  | ⟨2, _⟩ => Pi.single (0, 0) 1

private def cwScalar004Term (q : ℕ) : CWTerm q := Sum.inr 0

private def cwScalar004Selected (q : ℕ) (s : Fin 3) :
    Fin (q + 2) × Fin (q + 2) :=
  (cwTermTriple q (cwScalar004Term q) s,
    cwTermTriple q (cwScalar004Term q) s)

private theorem cwScalarOutput_tprod
    (K : Type u) [Field K] :
    tprod K (cwScalarOutput K) = MMTensor K 1 1 1 := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  congr 1

private theorem cwScalar004_mismatch_of_ne
    (q : ℕ) {t : CWTerm q} (ht : t ≠ cwScalar004Term q) :
    ∃ s : Fin 3,
      cwTermTriple q t s ≠ cwTermTriple q (cwScalar004Term q) s := by
  rcases t with ⟨i, r⟩ | r
  · fin_cases r
    · refine ⟨1, ?_⟩
      simp [cwScalar004Term, cwTermTriple, cwM, cwO]
    · refine ⟨0, ?_⟩
      simp [cwScalar004Term, cwTermTriple, cwM, cwO]
    · refine ⟨0, ?_⟩
      simp [cwScalar004Term, cwTermTriple, cwM, cwO]
  · fin_cases r
    · exact (ht rfl).elim
    · refine ⟨1, ?_⟩
      simp [cwScalar004Term, cwTermTriple, cwT, cwO]
    · refine ⟨0, ?_⟩
      simp [cwScalar004Term, cwTermTriple, cwT, cwO]

private theorem cwScalar004_term_pair
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    PiTensorProduct.map
        (cwSquareSelectorMap K q 1 1 1 (cwSquareBlockType 0 0 4)
          (cwScalar004Selected q) (cwScalarOutput K))
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s
            (cwSquareBlockType 0 0 4 s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      if t = cwScalar004Term q ∧ u = cwScalar004Term q then
        tprod K (cwScalarOutput K)
      else 0 := by
  rw [cwSquareSelectorMap_term_pair]
  by_cases ht : t = cwScalar004Term q
  · subst t
    by_cases hu : u = cwScalar004Term q
    · subst u
      simp only [true_and, if_true]
      congr 1
      funext s
      fin_cases s <;>
        simp [cwScalar004Term, cwScalar004Selected, cwTermTriple,
          cwSquareBlockType, cwSquarePairGrade, cwCoordGrade_O,
          cwCoordGrade_T]
    · simp only [true_and, hu, if_false]
      rcases cwScalar004_mismatch_of_ne q hu with ⟨s, hs⟩
      apply (PiTensorProduct.tprod K).map_coord_zero s
      split_ifs with hgrade hselected
      · exact (hs (congrArg Prod.snd hselected)).elim
      · rfl
      · rfl
  · simp only [ht, false_and, if_false]
    rcases cwScalar004_mismatch_of_ne q ht with ⟨s, hs⟩
    apply (PiTensorProduct.tprod K).map_coord_zero s
    split_ifs with hgrade hselected
    · exact (hs (congrArg Prod.fst hselected)).elim
    · rfl
    · rfl

private theorem cwSquareCanonical_scalar004
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) := by
  let maps := cwSquareSelectorMap K q 1 1 1
    (cwSquareBlockType 0 0 4) (cwScalar004Selected q) (cwScalarOutput K)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 0 4)) = MMTensor K 1 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwScalar004_term_pair]
  rw [cwScalarOutput_tprod]
  rw [Fintype.sum_eq_single (cwScalar004Term q)]
  · rw [Fintype.sum_eq_single (cwScalar004Term q)]
    · simp
    · intro u hu
      simp [hu]
  · intro t ht
    apply Fintype.sum_eq_zero
    intro u
    simp [ht]

private def cwScalarTerm (q : ℕ) (r : Fin 3) : CWTerm q := Sum.inr r

private def cwScalarSelected (q : ℕ) (r s : Fin 3) :
    Fin (q + 2) × Fin (q + 2) :=
  (cwTermTriple q (cwScalarTerm q r) s,
    cwTermTriple q (cwScalarTerm q r) s)

private def cwScalarBlock (r : Fin 3) : Fin 3 → Fin 5 :=
  match r with
  | ⟨0, _⟩ => cwSquareBlockType 0 0 4
  | ⟨1, _⟩ => cwSquareBlockType 0 4 0
  | ⟨2, _⟩ => cwSquareBlockType 4 0 0

private theorem cwScalar_mismatch_of_ne
    (q : ℕ) (r : Fin 3) {t : CWTerm q} (ht : t ≠ cwScalarTerm q r) :
    ∃ s : Fin 3,
      cwTermTriple q t s ≠ cwTermTriple q (cwScalarTerm q r) s := by
  rcases t with ⟨i, r'⟩ | r'
  · fin_cases r'
    · refine ⟨1, ?_⟩
      fin_cases r <;> simp [cwScalarTerm, cwTermTriple, cwM, cwO, cwT] <;> omega
    · refine ⟨0, ?_⟩
      fin_cases r <;> simp [cwScalarTerm, cwTermTriple, cwM, cwO, cwT] <;> omega
    · refine ⟨0, ?_⟩
      fin_cases r <;> simp [cwScalarTerm, cwTermTriple, cwM, cwO, cwT] <;> omega
  · fin_cases r
    · fin_cases r'
      · exact (ht rfl).elim
      · refine ⟨1, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
      · refine ⟨0, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
    · fin_cases r'
      · refine ⟨1, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
      · exact (ht rfl).elim
      · refine ⟨0, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
    · fin_cases r'
      · refine ⟨0, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
      · refine ⟨0, ?_⟩
        simp [cwScalarTerm, cwTermTriple, cwT, cwO]
      · exact (ht rfl).elim

private theorem cwScalar_term_pair
    (K : Type u) [Field K] (q : ℕ) (r : Fin 3) (t u : CWTerm q) :
    PiTensorProduct.map
        (cwSquareSelectorMap K q 1 1 1 (cwScalarBlock r)
          (cwScalarSelected q r) (cwScalarOutput K))
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s
            (cwScalarBlock r s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      if t = cwScalarTerm q r ∧ u = cwScalarTerm q r then
        tprod K (cwScalarOutput K)
      else 0 := by
  rw [cwSquareSelectorMap_term_pair]
  by_cases ht : t = cwScalarTerm q r
  · subst t
    by_cases hu : u = cwScalarTerm q r
    · subst u
      simp only [true_and, if_true]
      congr 1
      funext s
      fin_cases r <;> fin_cases s <;>
        simp [cwScalarTerm, cwScalarSelected, cwScalarBlock, cwTermTriple,
          cwSquareBlockType, cwSquarePairGrade, cwCoordGrade_O,
          cwCoordGrade_T]
    · simp only [true_and, hu, if_false]
      rcases cwScalar_mismatch_of_ne q r hu with ⟨s, hs⟩
      apply (PiTensorProduct.tprod K).map_coord_zero s
      split_ifs with hgrade hselected
      · exact (hs (congrArg Prod.snd hselected)).elim
      · rfl
      · rfl
  · simp only [ht, false_and, if_false]
    rcases cwScalar_mismatch_of_ne q r ht with ⟨s, hs⟩
    apply (PiTensorProduct.tprod K).map_coord_zero s
    split_ifs with hgrade hselected
    · exact (hs (congrArg Prod.fst hselected)).elim
    · rfl
    · rfl

private theorem cwSquareCanonical_scalar
    (K : Type u) [Field K] (q : ℕ) (r : Fin 3) :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor (cwScalarBlock r)) := by
  let maps := cwSquareSelectorMap K q 1 1 1
    (cwScalarBlock r) (cwScalarSelected q r) (cwScalarOutput K)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor (cwScalarBlock r)) =
        MMTensor K 1 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwScalar_term_pair]
  rw [cwScalarOutput_tprod]
  rw [Fintype.sum_eq_single (cwScalarTerm q r)]
  · rw [Fintype.sum_eq_single (cwScalarTerm q r)]
    · simp
    · intro u hu
      simp [hu]
  · intro t ht
    apply Fintype.sum_eq_zero
    intro u
    simp [ht]

private theorem cwSquareCanonical_scalar040
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) := by
  simpa [cwScalarBlock] using cwSquareCanonical_scalar K q (1 : Fin 3)

private theorem cwSquareCanonical_scalar400
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) := by
  simpa [cwScalarBlock] using cwSquareCanonical_scalar K q (2 : Fin 3)

-/

/- The rectangular and central calculations are separate elementary children. -/

private noncomputable def cwSquareBasisMap
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K]
      (MMObj K n m p).V s :=
  ((cwSquareCanonicalBasis K q s).constr K (output s)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareBasisMap K q n m p σ output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareCanonicalBasis K q s idx)) =
      if cwSquarePairGrade q idx = σ s then output s idx else 0 := by
  rw [cwSquareCanonical_blockProj_basis]
  split_ifs with hgrade
  · simp [cwSquareBasisMap, Module.Basis.constr_basis]
  · simp [cwSquareBasisMap]

private theorem cwSquareBasisMap_term_pair
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (t u : CWTerm q) :
    PiTensorProduct.map (cwSquareBasisMap K q n m p σ output)
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      tprod K (fun s =>
        if cwSquarePairGrade q
            (cwTermTriple q t s, cwTermTriple q u s) = σ s then
          output s (cwTermTriple q t s, cwTermTriple q u s)
        else 0) := by
  have hterm (r : CWTerm q) :
      cwTermMonom K q r =
        tprod K (fun s => cwVec K q s (cwTermTriple q r s)) := by
    unfold cwTermMonom CWMonom
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hterm t, hterm u]
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q t s)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q u s)
  change PiTensorProduct.map (cwSquareBasisMap K q n m p σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (tprod K v₁) (tprod K v₂))) = _
  have hinter := interchange_tprod (K := K) v₁ v₂
  refine (congrArg
    (fun z => PiTensorProduct.map (cwSquareBasisMap K q n m p σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s)) z)) hinter).trans ?_
  have hinner :
      PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (tprod K (fun i => v₁ i ⊗ₜ[K] v₂ i)) =
        tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s)) :=
    PiTensorProduct.map_tprod _ _
  calc
    _ = PiTensorProduct.map (cwSquareBasisMap K q n m p σ output)
        (tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) := congrArg _ hinner
    _ = tprod K (fun s =>
        cwSquareBasisMap K q n m p σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      PiTensorProduct.map_tprod _ _
    _ = _ := by
      congr 1
      funext s
      dsimp [v₁, v₂]
      have hbasis := (cwSquareBasis_apply K q s
        (cwTermTriple q t s) (cwTermTriple q u s)).symm
      refine (congrArg
        (fun z => cwSquareBasisMap K q n m p σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s) z)) hbasis).trans ?_
      exact cwSquareBasisMap_apply_blockProj_basis
        K q n m p σ output s _

/- Superseded by the finite-sum rectangular router below.  Kept temporarily
inside a comment while the canonical proof is being consolidated. -/
/-
private theorem cwM_injective (q : ℕ) : Function.Injective (cwM q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cwM] at hv
  omega

private theorem cwM_eq_iff (q : ℕ) (i j : Fin q) :
    cwM q i = cwM q j ↔ i = j :=
  (cwM_injective q).eq_iff

private theorem cwM_ne_O (q : ℕ) (i : Fin q) : cwM q i ≠ cwO q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwM, cwO] at hv
  omega

private theorem cwM_ne_T (q : ℕ) (i : Fin q) : cwM q i ≠ cwT q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwM, cwT] at hv
  omega

private def cwDoubleIndexEquiv (q : ℕ) :
    Fin q ⊕ Fin q ≃ Fin (2 * q) :=
  finSumFinEquiv.trans (finCongr (by omega))

private def cwRect013Vec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (2 * q)) :
    ∀ s : Fin 3, (MMObj K 1 1 (2 * q)).V s
  | ⟨0, _⟩ => Pi.single (0, 0) 1
  | ⟨1, _⟩ => Pi.single (0, k) 1
  | ⟨2, _⟩ => Pi.single (k, 0) 1

private noncomputable def cwRect013Output
    (K : Type u) [Field K] (q : ℕ) : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K 1 1 (2 * q)).V s
  | ⟨0, _⟩, idx =>
      if idx = (cwO q, cwO q) then Pi.single (0, 0) 1 else 0
  | ⟨1, _⟩, idx => fun jk =>
      match (cwDoubleIndexEquiv q).symm jk.2 with
      | Sum.inl i => if idx = (cwO q, cwM q i) then 1 else 0
      | Sum.inr i => if idx = (cwM q i, cwO q) then 1 else 0
  | ⟨2, _⟩, idx => fun ki =>
      match (cwDoubleIndexEquiv q).symm ki.1 with
      | Sum.inl i => if idx = (cwT q, cwM q i) then 1 else 0
      | Sum.inr i => if idx = (cwM q i, cwT q) then 1 else 0

private theorem cwRect013Output_zero_mode
    (K : Type u) [Field K] (q : ℕ) (k : Fin (2 * q)) :
    cwRect013Output K q 0 (cwO q, cwO q) = cwRect013Vec K q k 0 := by
  simp [cwRect013Output, cwRect013Vec]

private theorem cwRect013Output_one_left
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    cwRect013Output K q 1 (cwO q, cwM q i) =
      cwRect013Vec K q (cwDoubleIndexEquiv q (Sum.inl i)) 1 := by
  funext jk
  rcases jk with ⟨j, k⟩
  fin_cases j
  generalize hsplit : (cwDoubleIndexEquiv q).symm k = z
  rcases z with a | a
  · have hk : k = cwDoubleIndexEquiv q (Sum.inl a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_O, Pi.single_apply]
  · have hk : k = cwDoubleIndexEquiv q (Sum.inr a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_O, Pi.single_apply]

private theorem cwRect013Output_one_right
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    cwRect013Output K q 1 (cwM q i, cwO q) =
      cwRect013Vec K q (cwDoubleIndexEquiv q (Sum.inr i)) 1 := by
  funext jk
  rcases jk with ⟨j, k⟩
  fin_cases j
  generalize hsplit : (cwDoubleIndexEquiv q).symm k = z
  rcases z with a | a
  · have hk : k = cwDoubleIndexEquiv q (Sum.inl a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_O, Pi.single_apply]
  · have hk : k = cwDoubleIndexEquiv q (Sum.inr a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_O, Pi.single_apply]

private theorem cwRect013Output_two_left
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    cwRect013Output K q 2 (cwT q, cwM q i) =
      cwRect013Vec K q (cwDoubleIndexEquiv q (Sum.inl i)) 2 := by
  funext ki
  rcases ki with ⟨k, j⟩
  fin_cases j
  generalize hsplit : (cwDoubleIndexEquiv q).symm k = z
  rcases z with a | a
  · have hk : k = cwDoubleIndexEquiv q (Sum.inl a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_T, Pi.single_apply]
  · have hk : k = cwDoubleIndexEquiv q (Sum.inr a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_T, Pi.single_apply]

private theorem cwRect013Output_two_right
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    cwRect013Output K q 2 (cwM q i, cwT q) =
      cwRect013Vec K q (cwDoubleIndexEquiv q (Sum.inr i)) 2 := by
  funext ki
  rcases ki with ⟨k, j⟩
  fin_cases j
  generalize hsplit : (cwDoubleIndexEquiv q).symm k = z
  rcases z with a | a
  · have hk : k = cwDoubleIndexEquiv q (Sum.inl a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_T, Pi.single_apply]
  · have hk : k = cwDoubleIndexEquiv q (Sum.inr a) := by
      rw [← (cwDoubleIndexEquiv q).apply_symm_apply k, hsplit]
    subst k
    simp [cwRect013Output, cwRect013Vec, cwM_eq_iff,
      cwM_ne_T, Pi.single_apply]
-/

private def cwRectLeft (q : ℕ) (i : Fin q) : Fin (2 * q) :=
  ⟨i.val, by omega⟩

private def cwRectRight (q : ℕ) (i : Fin q) : Fin (2 * q) :=
  ⟨q + i.val, by omega⟩

private noncomputable def cwRect013XVec
    (K : Type u) [Field K] (q : ℕ) :
    (MMObj K 1 1 (2 * q)).V (0 : Fin 3) :=
  (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private noncomputable def cwRect013MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (2 * q)) :
    ∀ s : Fin 3, (MMObj K 1 1 (2 * q)).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (2 * q) → K)
  | ⟨2, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (2 * q) × Fin 1 → K)

private noncomputable def cwRect013BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 1 (2 * q)).V s :=
  match s with
  | ⟨0, _⟩ =>
      if ab = (cwO q, cwO q) then cwRect013XVec K q else 0
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect013MMVec K q (cwRectLeft q i) 1 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect013MMVec K q (cwRectRight q i) 1 else 0)
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect013MMVec K q (cwRectLeft q i) 2 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect013MMVec K q (cwRectRight q i) 2 else 0)

private theorem cwM_injective' (q : ℕ) : Function.Injective (cwM q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cwM] at hv
  omega

private theorem cwM_eq_cwM_iff (q : ℕ) (i j : Fin q) :
    cwM q i = cwM q j ↔ i = j :=
  (cwM_injective' q).eq_iff

private theorem cwO_ne_cwM (q : ℕ) (i : Fin q) : cwO q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwM] at hv
  omega

private theorem cwT_ne_cwM (q : ℕ) (i : Fin q) : cwT q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwT, cwM] at hv
  omega

private theorem cwO_ne_cwT (q : ℕ) : cwO q ≠ cwT q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwT] at hv
  omega

private theorem cwM_ne_cwO (q : ℕ) (i : Fin q) : cwM q i ≠ cwO q :=
  (cwO_ne_cwM q i).symm

private theorem cwM_ne_cwT (q : ℕ) (i : Fin q) : cwM q i ≠ cwT q :=
  (cwT_ne_cwM q i).symm

private noncomputable def cwRectChannelEquiv (q : ℕ) :
    Fin q ⊕ Fin q ≃ Fin (2 * q) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem cwRectChannelEquiv_inl (q : ℕ) (i : Fin q) :
    cwRectChannelEquiv q (Sum.inl i) = cwRectLeft q i := by
  apply Fin.ext
  rfl

private theorem cwRectChannelEquiv_inr (q : ℕ) (i : Fin q) :
    cwRectChannelEquiv q (Sum.inr i) = cwRectRight q i := by
  apply Fin.ext
  rfl

private theorem MMTensor_rect013_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K 1 1 (2 * q) =
      ∑ k : Fin (2 * q), tprod K (cwRect013MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwRect013_two_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, tprod K (cwRect013MMVec K q (cwRectLeft q i))) +
      (∑ i : Fin q, tprod K (cwRect013MMVec K q (cwRectRight q i))) =
        MMTensor K 1 1 (2 * q) := by
  rw [MMTensor_rect013_channels]
  rw [← Equiv.sum_comp (cwRectChannelEquiv q)
    (fun k : Fin (2 * q) => tprod K (cwRect013MMVec K q k))]
  rw [Fintype.sum_sum_type]
  rfl

private def cwRectTermTriple (q : ℕ) :
    CWTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwT q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwO q

private theorem cwRectTermTriple_eq_cwTermTriple
    (q : ℕ) (t : CWTerm q) (s : Fin 3) :
    cwRectTermTriple q t s = cwTermTriple q t s := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;> fin_cases s <;> rfl

private noncomputable def cwRect013ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 1 (2 * q)).V
  | Sum.inr ⟨0, _⟩, Sum.inl (i, ⟨0, _⟩) =>
      tprod K (cwRect013MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨0, _⟩), Sum.inr ⟨0, _⟩ =>
      tprod K (cwRect013MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect013_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (0 : Fin 3) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inr (0 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 3 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect013ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 1 3 s) :
    cwRect013ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect013ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect013_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 0 1 3 s then
        cwRect013BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) =
        cwRect013ExpectedTermPair K q t u := by
  rcases cwRect013_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect013ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect013BasisOut, cwRect013MMVec,
        cwRect013XVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect013ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect013BasisOut, cwRect013MMVec,
        cwRect013XVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect013ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect013ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect013ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect013_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 0 1 3 s then
          cwRect013BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 1 (2 * q) := by
  simp_rw [cwRect013_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect013ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect013_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect013
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) := by
  let maps := cwSquareBasisMap K q 1 1 (2 * q)
    (cwSquareBlockType 0 1 3) (cwRect013BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 1 3)) = MMTensor K 1 1 (2 * q)
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect013_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwRect031BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 1 (2 * q)).V s :=
  match s with
  | ⟨0, _⟩ =>
      if ab = (cwO q, cwO q) then cwRect013XVec K q else 0
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect013MMVec K q (cwRectLeft q i) 1 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect013MMVec K q (cwRectRight q i) 1 else 0)
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect013MMVec K q (cwRectLeft q i) 2 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect013MMVec K q (cwRectRight q i) 2 else 0)

private noncomputable def cwRect031ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 1 (2 * q)).V
  | Sum.inr ⟨1, _⟩, Sum.inl (i, ⟨0, _⟩) =>
      tprod K (cwRect013MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨0, _⟩), Sum.inr ⟨1, _⟩ =>
      tprod K (cwRect013MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect031_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (1 : Fin 3) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inr (1 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 3 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect031ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 3 1 s) :
    cwRect031ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect031ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect031_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 0 3 1 s then
        cwRect031BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwRect031ExpectedTermPair K q t u := by
  rcases cwRect031_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect031ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect031BasisOut, cwRect013MMVec,
        cwRect013XVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect031ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect031BasisOut, cwRect013MMVec,
        cwRect013XVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect031ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect031ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect031ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect031_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 0 3 1 s then
          cwRect031BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 1 (2 * q) := by
  simp_rw [cwRect031_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect031ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect013_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect031
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) := by
  let maps := cwSquareBasisMap K q 1 1 (2 * q)
    (cwSquareBlockType 0 3 1) (cwRect031BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 3 1)) = MMTensor K 1 1 (2 * q)
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect031_all_filtered_term_pairs_eq_MMTensor K q

/- Central fields and the remaining rectangular orientations are separate children. -/
/-

private noncomputable def cwCentralIndexEquiv (q : ℕ) :
    (Fin 2 ⊕ (Fin q × Fin q)) ≃ Fin (q ^ 2 + 2) :=
  (Equiv.sumCongr (Equiv.refl (Fin 2)) finProdFinEquiv).trans <|
    finSumFinEquiv.trans (finCongr (by simp [pow_two, Nat.add_comm]))

private noncomputable def cwCentral022MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K 1 1 (q ^ 2 + 2)).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (q ^ 2 + 2) → K)
  | ⟨2, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (q ^ 2 + 2) × Fin 1 → K)

private noncomputable def cwCentral022BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 1 (q ^ 2 + 2)).V s :=
  match s with
  | ⟨0, _⟩ =>
      if ab = (cwO q, cwO q) then
        cwCentral022MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 0
      else 0
  | ⟨1, _⟩ =>
      (if ab = (cwO q, cwT q) then
        cwCentral022MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 1
      else 0) +
      (if ab = (cwT q, cwO q) then
        cwCentral022MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 1
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral022MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 1
        else 0)
  | ⟨2, _⟩ =>
      (if ab = (cwT q, cwO q) then
        cwCentral022MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 2
      else 0) +
      (if ab = (cwO q, cwT q) then
        cwCentral022MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 2
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral022MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 2
        else 0)

private theorem MMTensor_central022_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K 1 1 (q ^ 2 + 2) =
      ∑ k : Fin (q ^ 2 + 2), tprod K (cwCentral022MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwCentral022_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    tprod K (cwCentral022MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0))) +
      tprod K (cwCentral022MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1))) +
      (∑ i : Fin q, ∑ j : Fin q,
        tprod K (cwCentral022MMVec K q
          (cwCentralIndexEquiv q (Sum.inr (i, j))))) =
        MMTensor K 1 1 (q ^ 2 + 2) := by
  rw [MMTensor_central022_channels]
  rw [← Equiv.sum_comp (cwCentralIndexEquiv q)
    (fun k : Fin (q ^ 2 + 2) => tprod K (cwCentral022MMVec K q k))]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_prod_type]

private noncomputable def cwCentral022ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 1 (q ^ 2 + 2)).V
  | Sum.inr ⟨0, _⟩, Sum.inr ⟨1, _⟩ =>
      tprod K (cwCentral022MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0)))
  | Sum.inr ⟨1, _⟩, Sum.inr ⟨0, _⟩ =>
      tprod K (cwCentral022MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1)))
  | Sum.inl (i, ⟨0, _⟩), Sum.inl (j, ⟨0, _⟩) =>
      tprod K (cwCentral022MMVec K q
        (cwCentralIndexEquiv q (Sum.inr (i, j))))
  | _, _ => 0

private theorem cwCentral022_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (t = Sum.inr (0 : Fin 3) ∧ u = Sum.inr (1 : Fin 3)) ∨
    (t = Sum.inr (1 : Fin 3) ∧ u = Sum.inr (0 : Fin 3)) ∨
    (∃ i j : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inl (j, (0 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 2 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCentral022ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 2 2 s) :
    cwCentral022ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCentral022ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

@[simp] private theorem sum_sum_ite_pair_eq
    {A : Type*} [AddCommMonoid A] {q : ℕ}
    (f : Fin q → Fin q → A) (i j : Fin q) :
    (∑ x : Fin q, ∑ y : Fin q,
      if i = x ∧ j = y then f x y else 0) = f i j := by
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro y hy
      simp [Ne.symm hy]
  · intro x hx
    simp [Ne.symm hx]

private theorem cwCentral022_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 0 2 2 s then
        cwCentral022BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCentral022ExpectedTermPair K q t u := by
  rcases cwCentral022_special_or_grade_mismatch q t u with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCentral022ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral022BasisOut, cwCentral022MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral022ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral022BasisOut, cwCentral022MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral022ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral022BasisOut, cwCentral022MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
  · rw [cwCentral022ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCentral022ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCentral022ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCentral022_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 0 2 2 s then
          cwCentral022BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 1 (q ^ 2 + 2) := by
  simp_rw [cwCentral022_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwCentral022ExpectedTermPair, Fin.sum_univ_succ]
  rw [← cwCentral022_family_sum_eq_MMTensor K q]
  abel

private theorem cwSquareCanonical_central022
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)) := by
  let maps := cwSquareBasisMap K q 1 1 (q ^ 2 + 2)
    (cwSquareBlockType 0 2 2) (cwCentral022BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 2 2)) = MMTensor K 1 1 (q ^ 2 + 2)
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCentral022_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwCentral202MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K (q ^ 2 + 2) 1 1).V s
  | ⟨0, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (q ^ 2 + 2) × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (q ^ 2 + 2) → K)

private noncomputable def cwCentral202BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K (q ^ 2 + 2) 1 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (if ab = (cwO q, cwT q) then
        cwCentral202MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 0
      else 0) +
      (if ab = (cwT q, cwO q) then
        cwCentral202MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 0
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral202MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 0
        else 0)
  | ⟨1, _⟩ =>
      if ab = (cwO q, cwO q) then
        cwCentral202MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 1
      else 0
  | ⟨2, _⟩ =>
      (if ab = (cwT q, cwO q) then
        cwCentral202MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 2
      else 0) +
      (if ab = (cwO q, cwT q) then
        cwCentral202MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 2
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral202MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 2
        else 0)

private theorem MMTensor_central202_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K (q ^ 2 + 2) 1 1 =
      ∑ k : Fin (q ^ 2 + 2), tprod K (cwCentral202MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwCentral202_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    tprod K (cwCentral202MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0))) +
      tprod K (cwCentral202MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1))) +
      (∑ i : Fin q, ∑ j : Fin q,
        tprod K (cwCentral202MMVec K q
          (cwCentralIndexEquiv q (Sum.inr (i, j))))) =
        MMTensor K (q ^ 2 + 2) 1 1 := by
  rw [MMTensor_central202_channels]
  rw [← Equiv.sum_comp (cwCentralIndexEquiv q)
    (fun k : Fin (q ^ 2 + 2) => tprod K (cwCentral202MMVec K q k))]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_prod_type]

private noncomputable def cwCentral202ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K (q ^ 2 + 2) 1 1).V
  | Sum.inr ⟨0, _⟩, Sum.inr ⟨2, _⟩ =>
      tprod K (cwCentral202MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0)))
  | Sum.inr ⟨2, _⟩, Sum.inr ⟨0, _⟩ =>
      tprod K (cwCentral202MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1)))
  | Sum.inl (i, ⟨1, _⟩), Sum.inl (j, ⟨1, _⟩) =>
      tprod K (cwCentral202MMVec K q
        (cwCentralIndexEquiv q (Sum.inr (i, j))))
  | _, _ => 0

private theorem cwCentral202_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (t = Sum.inr (0 : Fin 3) ∧ u = Sum.inr (2 : Fin 3)) ∨
    (t = Sum.inr (2 : Fin 3) ∧ u = Sum.inr (0 : Fin 3)) ∨
    (∃ i j : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inl (j, (1 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 2 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCentral202ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 2 0 2 s) :
    cwCentral202ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCentral202ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwCentral202_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 2 0 2 s then
        cwCentral202BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCentral202ExpectedTermPair K q t u := by
  rcases cwCentral202_special_or_grade_mismatch q t u with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCentral202ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral202BasisOut, cwCentral202MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral202ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral202BasisOut, cwCentral202MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral202ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral202BasisOut, cwCentral202MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
  · rw [cwCentral202ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCentral202ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCentral202ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCentral202_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 2 0 2 s then
          cwCentral202BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K (q ^ 2 + 2) 1 1 := by
  simp_rw [cwCentral202_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwCentral202ExpectedTermPair, Fin.sum_univ_succ]
  rw [← cwCentral202_family_sum_eq_MMTensor K q]
  abel

private theorem cwSquareCanonical_central202
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)) := by
  let maps := cwSquareBasisMap K q (q ^ 2 + 2) 1 1
    (cwSquareBlockType 2 0 2) (cwCentral202BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 2 0 2)) = MMTensor K (q ^ 2 + 2) 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCentral202_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwCentral220MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K 1 (q ^ 2 + 2) 1).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (q ^ 2 + 2) → K)
  | ⟨1, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (q ^ 2 + 2) × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private noncomputable def cwCentral220BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 (q ^ 2 + 2) 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (if ab = (cwO q, cwT q) then
        cwCentral220MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 0
      else 0) +
      (if ab = (cwT q, cwO q) then
        cwCentral220MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 0
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral220MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 0
        else 0)
  | ⟨1, _⟩ =>
      (if ab = (cwT q, cwO q) then
        cwCentral220MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 1
      else 0) +
      (if ab = (cwO q, cwT q) then
        cwCentral220MMVec K q (cwCentralIndexEquiv q (Sum.inl 1)) 1
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          cwCentral220MMVec K q
            (cwCentralIndexEquiv q (Sum.inr (i, j))) 1
        else 0)
  | ⟨2, _⟩ =>
      if ab = (cwO q, cwO q) then
        cwCentral220MMVec K q (cwCentralIndexEquiv q (Sum.inl 0)) 2
      else 0

private theorem MMTensor_central220_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K 1 (q ^ 2 + 2) 1 =
      ∑ k : Fin (q ^ 2 + 2), tprod K (cwCentral220MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwCentral220_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    tprod K (cwCentral220MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0))) +
      tprod K (cwCentral220MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1))) +
      (∑ i : Fin q, ∑ j : Fin q,
        tprod K (cwCentral220MMVec K q
          (cwCentralIndexEquiv q (Sum.inr (i, j))))) =
        MMTensor K 1 (q ^ 2 + 2) 1 := by
  rw [MMTensor_central220_channels]
  rw [← Equiv.sum_comp (cwCentralIndexEquiv q)
    (fun k : Fin (q ^ 2 + 2) => tprod K (cwCentral220MMVec K q k))]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fintype.sum_prod_type]

private noncomputable def cwCentral220ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 (q ^ 2 + 2) 1).V
  | Sum.inr ⟨1, _⟩, Sum.inr ⟨2, _⟩ =>
      tprod K (cwCentral220MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 0)))
  | Sum.inr ⟨2, _⟩, Sum.inr ⟨1, _⟩ =>
      tprod K (cwCentral220MMVec K q
        (cwCentralIndexEquiv q (Sum.inl 1)))
  | Sum.inl (i, ⟨2, _⟩), Sum.inl (j, ⟨2, _⟩) =>
      tprod K (cwCentral220MMVec K q
        (cwCentralIndexEquiv q (Sum.inr (i, j))))
  | _, _ => 0

private theorem cwCentral220_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (t = Sum.inr (1 : Fin 3) ∧ u = Sum.inr (2 : Fin 3)) ∨
    (t = Sum.inr (2 : Fin 3) ∧ u = Sum.inr (1 : Fin 3)) ∨
    (∃ i j : Fin q,
      t = Sum.inl (i, (2 : Fin 3)) ∧ u = Sum.inl (j, (2 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCentral220ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 2 2 0 s) :
    cwCentral220ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCentral220ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwCentral220_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 2 2 0 s then
        cwCentral220BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCentral220ExpectedTermPair K q t u := by
  rcases cwCentral220_special_or_grade_mismatch q t u with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCentral220ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral220BasisOut, cwCentral220MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral220ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral220BasisOut, cwCentral220MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral220ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral220BasisOut, cwCentral220MMVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
  · rw [cwCentral220ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCentral220ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCentral220ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCentral220_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 2 2 0 s then
          cwCentral220BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 (q ^ 2 + 2) 1 := by
  simp_rw [cwCentral220_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwCentral220ExpectedTermPair, Fin.sum_univ_succ]
  rw [← cwCentral220_family_sum_eq_MMTensor K q]
  abel

private theorem cwSquareCanonical_central220
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by
  let maps := cwSquareBasisMap K q 1 (q ^ 2 + 2) 1
    (cwSquareBlockType 2 2 0) (cwCentral220BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 2 2 0)) = MMTensor K 1 (q ^ 2 + 2) 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCentral220_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwRect103MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (2 * q)) :
    ∀ s : Fin 3, (MMObj K (2 * q) 1 1).V s
  | ⟨0, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (2 * q) × Fin 1 → K)
  | ⟨1, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (2 * q) → K)

private theorem MMTensor_rect103_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K (2 * q) 1 1 =
      ∑ k : Fin (2 * q), tprod K (cwRect103MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwRect103_two_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, tprod K (cwRect103MMVec K q (cwRectLeft q i))) +
      (∑ i : Fin q, tprod K (cwRect103MMVec K q (cwRectRight q i))) =
        MMTensor K (2 * q) 1 1 := by
  rw [MMTensor_rect103_channels]
  rw [← Equiv.sum_comp (cwRectChannelEquiv q)
    (fun k : Fin (2 * q) => tprod K (cwRect103MMVec K q k))]
  rw [Fintype.sum_sum_type]
  rfl

private noncomputable def cwRect103YVec
    (K : Type u) [Field K] (q : ℕ) :
    (MMObj K (2 * q) 1 1).V (1 : Fin 3) :=
  (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private noncomputable def cwRect103BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K (2 * q) 1 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect103MMVec K q (cwRectLeft q i) 0 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect103MMVec K q (cwRectRight q i) 0 else 0)
  | ⟨1, _⟩ =>
      if ab = (cwO q, cwO q) then
        cwRect103YVec K q
      else 0
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect103MMVec K q (cwRectLeft q i) 2 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect103MMVec K q (cwRectRight q i) 2 else 0)

private noncomputable def cwRect103ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K (2 * q) 1 1).V
  | Sum.inr ⟨0, _⟩, Sum.inl (i, ⟨1, _⟩) =>
      tprod K (cwRect103MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨1, _⟩), Sum.inr ⟨0, _⟩ =>
      tprod K (cwRect103MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect103_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (0 : Fin 3) ∧ u = Sum.inl (i, (1 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inr (0 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 3 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect103ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 1 0 3 s) :
    cwRect103ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect103ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect103_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 1 0 3 s then
        cwRect103BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwRect103ExpectedTermPair K q t u := by
  rcases cwRect103_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect103ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect103BasisOut, cwRect103MMVec,
        cwRect103YVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect103ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect103BasisOut, cwRect103MMVec,
        cwRect103YVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect103ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect103ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect103ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect103_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 1 0 3 s then
          cwRect103BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K (2 * q) 1 1 := by
  simp_rw [cwRect103_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect103ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect103_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect103
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 0 3)) := by
  let maps := cwSquareBasisMap K q (2 * q) 1 1
    (cwSquareBlockType 1 0 3) (cwRect103BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 1 0 3)) = MMTensor K (2 * q) 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect103_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwRect301BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K (2 * q) 1 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect103MMVec K q (cwRectLeft q i) 0 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect103MMVec K q (cwRectRight q i) 0 else 0)
  | ⟨1, _⟩ =>
      if ab = (cwO q, cwO q) then cwRect103YVec K q else 0
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect103MMVec K q (cwRectLeft q i) 2 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect103MMVec K q (cwRectRight q i) 2 else 0)

private noncomputable def cwRect301ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K (2 * q) 1 1).V
  | Sum.inr ⟨2, _⟩, Sum.inl (i, ⟨1, _⟩) =>
      tprod K (cwRect103MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨1, _⟩), Sum.inr ⟨2, _⟩ =>
      tprod K (cwRect103MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect301_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (2 : Fin 3) ∧ u = Sum.inl (i, (1 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inr (2 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 3 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 0 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect301ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 3 0 1 s) :
    cwRect301ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect301ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect301_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 3 0 1 s then
        cwRect301BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwRect301ExpectedTermPair K q t u := by
  rcases cwRect301_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect301ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect301BasisOut, cwRect103MMVec,
        cwRect103YVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect301ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect301BasisOut, cwRect103MMVec,
        cwRect103YVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect301ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect301ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect301ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect301_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 3 0 1 s then
          cwRect301BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K (2 * q) 1 1 := by
  simp_rw [cwRect301_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect301ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect103_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect301
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 0 1)) := by
  let maps := cwSquareBasisMap K q (2 * q) 1 1
    (cwSquareBlockType 3 0 1) (cwRect301BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 3 0 1)) = MMTensor K (2 * q) 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect301_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwRect130MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (2 * q)) :
    ∀ s : Fin 3, (MMObj K 1 (2 * q) 1).V s
  | ⟨0, _⟩ =>
      (Pi.single ((0 : Fin 1), k) 1 : Fin 1 × Fin (2 * q) → K)
  | ⟨1, _⟩ =>
      (Pi.single (k, (0 : Fin 1)) 1 : Fin (2 * q) × Fin 1 → K)
  | ⟨2, _⟩ =>
      (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private theorem MMTensor_rect130_channels
    (K : Type u) [Field K] (q : ℕ) :
    MMTensor K 1 (2 * q) 1 =
      ∑ k : Fin (2 * q), tprod K (cwRect130MMVec K q k) := by
  unfold MMTensor
  simp only [Fin.sum_univ_one]
  apply Finset.sum_congr rfl
  intro k hk
  congr 1

private theorem cwRect130_two_family_sum_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, tprod K (cwRect130MMVec K q (cwRectLeft q i))) +
      (∑ i : Fin q, tprod K (cwRect130MMVec K q (cwRectRight q i))) =
        MMTensor K 1 (2 * q) 1 := by
  rw [MMTensor_rect130_channels]
  rw [← Equiv.sum_comp (cwRectChannelEquiv q)
    (fun k : Fin (2 * q) => tprod K (cwRect130MMVec K q k))]
  rw [Fintype.sum_sum_type]
  rfl

private noncomputable def cwRect130ZVec
    (K : Type u) [Field K] (q : ℕ) :
    (MMObj K 1 (2 * q) 1).V (2 : Fin 3) :=
  (Pi.single ((0 : Fin 1), (0 : Fin 1)) 1 : Fin 1 × Fin 1 → K)

private noncomputable def cwRect130BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 (2 * q) 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect130MMVec K q (cwRectLeft q i) 0 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect130MMVec K q (cwRectRight q i) 0 else 0)
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect130MMVec K q (cwRectLeft q i) 1 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect130MMVec K q (cwRectRight q i) 1 else 0)
  | ⟨2, _⟩ =>
      if ab = (cwO q, cwO q) then cwRect130ZVec K q else 0

private noncomputable def cwRect130ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 (2 * q) 1).V
  | Sum.inr ⟨1, _⟩, Sum.inl (i, ⟨2, _⟩) =>
      tprod K (cwRect130MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨2, _⟩), Sum.inr ⟨1, _⟩ =>
      tprod K (cwRect130MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect130_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (1 : Fin 3) ∧ u = Sum.inl (i, (2 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (2 : Fin 3)) ∧ u = Sum.inr (1 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 3 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect130ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 1 3 0 s) :
    cwRect130ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect130ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect130_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 1 3 0 s then
        cwRect130BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwRect130ExpectedTermPair K q t u := by
  rcases cwRect130_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect130ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect130BasisOut, cwRect130MMVec,
        cwRect130ZVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect130ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect130BasisOut, cwRect130MMVec,
        cwRect130ZVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect130ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect130ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect130ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect130_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 1 3 0 s then
          cwRect130BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 (2 * q) 1 := by
  simp_rw [cwRect130_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect130ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect130_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect130
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 3 0)) := by
  let maps := cwSquareBasisMap K q 1 (2 * q) 1
    (cwSquareBlockType 1 3 0) (cwRect130BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 1 3 0)) = MMTensor K 1 (2 * q) 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect130_all_filtered_term_pairs_eq_MMTensor K q

private noncomputable def cwRect310BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 (2 * q) 1).V s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwT q, cwM q i) then
          cwRect130MMVec K q (cwRectLeft q i) 0 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwT q) then
          cwRect130MMVec K q (cwRectRight q i) 0 else 0)
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          cwRect130MMVec K q (cwRectLeft q i) 1 else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          cwRect130MMVec K q (cwRectRight q i) 1 else 0)
  | ⟨2, _⟩ =>
      if ab = (cwO q, cwO q) then cwRect130ZVec K q else 0

private noncomputable def cwRect310ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (MMObj K 1 (2 * q) 1).V
  | Sum.inr ⟨2, _⟩, Sum.inl (i, ⟨2, _⟩) =>
      tprod K (cwRect130MMVec K q (cwRectLeft q i))
  | Sum.inl (i, ⟨2, _⟩), Sum.inr ⟨2, _⟩ =>
      tprod K (cwRect130MMVec K q (cwRectRight q i))
  | _, _ => 0

private theorem cwRect310_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (2 : Fin 3) ∧ u = Sum.inl (i, (2 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (2 : Fin 3)) ∧ u = Sum.inr (2 : Fin 3)) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 3 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect310ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 3 1 0 s) :
    cwRect310ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect310ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect310_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 3 1 0 s then
        cwRect310BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwRect310ExpectedTermPair K q t u := by
  rcases cwRect310_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwRect310ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect310BasisOut, cwRect130MMVec,
        cwRect130ZVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect310ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect310BasisOut, cwRect130MMVec,
        cwRect130ZVec, cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · rw [cwRect310ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwRect310ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwRect310ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwRect310_all_filtered_term_pairs_eq_MMTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 3 1 0 s then
          cwRect310BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = MMTensor K 1 (2 * q) 1 := by
  simp_rw [cwRect310_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwRect310ExpectedTermPair, Fin.sum_univ_succ]
  rw [add_comm]
  exact cwRect130_two_family_sum_eq_MMTensor K q

private theorem cwSquareCanonical_rect310
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 1 0)) := by
  let maps := cwSquareBasisMap K q 1 (2 * q) 1
    (cwSquareBlockType 3 1 0) (cwRect310BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 3 1 0)) = MMTensor K 1 (2 * q) 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwRect310_all_filtered_term_pairs_eq_MMTensor K q

-/

/- Coupled-child duplicates of the rectangular routing API. -/
/-
private theorem cwM_injective' (q : ℕ) : Function.Injective (cwM q) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [cwM] at hv
  omega

private theorem cwM_eq_cwM_iff (q : ℕ) (i j : Fin q) :
    cwM q i = cwM q j ↔ i = j :=
  (cwM_injective' q).eq_iff

private theorem cwO_ne_cwM (q : ℕ) (i : Fin q) : cwO q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwM] at hv
  omega

private theorem cwT_ne_cwM (q : ℕ) (i : Fin q) : cwT q ≠ cwM q i := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwT, cwM] at hv
  omega

private theorem cwO_ne_cwT (q : ℕ) : cwO q ≠ cwT q := by
  intro h
  have hv := congrArg Fin.val h
  simp only [cwO, cwT] at hv
  omega

private theorem cwM_ne_cwO (q : ℕ) (i : Fin q) : cwM q i ≠ cwO q :=
  (cwO_ne_cwM q i).symm

private theorem cwM_ne_cwT (q : ℕ) (i : Fin q) : cwM q i ≠ cwT q :=
  (cwT_ne_cwM q i).symm

private def cwRectTermTriple (q : ℕ) :
    CWTerm q → Fin 3 → Fin (q + 2)
  | Sum.inl (i, ⟨0, _⟩), ⟨0, _⟩ => cwO q
  | Sum.inl (i, ⟨0, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨0, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨1, _⟩), ⟨1, _⟩ => cwO q
  | Sum.inl (i, ⟨1, _⟩), ⟨2, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨0, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨1, _⟩ => cwM q i
  | Sum.inl (i, ⟨2, _⟩), ⟨2, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨0, _⟩, ⟨2, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨0, _⟩ => cwO q
  | Sum.inr ⟨1, _⟩, ⟨1, _⟩ => cwT q
  | Sum.inr ⟨1, _⟩, ⟨2, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨0, _⟩ => cwT q
  | Sum.inr ⟨2, _⟩, ⟨1, _⟩ => cwO q
  | Sum.inr ⟨2, _⟩, ⟨2, _⟩ => cwO q

private theorem cwRectTermTriple_eq_cwTermTriple
    (q : ℕ) (t : CWTerm q) (s : Fin 3) :
    cwRectTermTriple q t s = cwTermTriple q t s := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;> fin_cases s <;> rfl

private noncomputable def cwSquareTargetBasisMap
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K] W s :=
  ((cwSquareCanonicalBasis K q s).constr K (output s)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareTargetBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareTargetBasisMap K q W σ output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareCanonicalBasis K q s idx)) =
      if cwSquarePairGrade q idx = σ s then output s idx else 0 := by
  rw [cwSquareCanonical_blockProj_basis]
  split_ifs with hgrade
  · simp [cwSquareTargetBasisMap]
  · simp [cwSquareTargetBasisMap]

private theorem cwSquareTargetBasisMap_term_pair
    (K : Type u) [Field K] (q : ℕ)
    (W : Fin 3 → Type u)
    [∀ s, AddCommGroup (W s)] [∀ s, Module K (W s)]
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → W s)
    (t u : CWTerm q) :
    PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      tprod K (fun s =>
        if cwSquarePairGrade q
            (cwTermTriple q t s, cwTermTriple q u s) = σ s then
          output s (cwTermTriple q t s, cwTermTriple q u s)
        else 0) := by
  have hterm (r : CWTerm q) :
      cwTermMonom K q r =
        tprod K (fun s => cwVec K q s (cwTermTriple q r s)) := by
    unfold cwTermMonom CWMonom
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hterm t, hterm u]
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q t s)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q u s)
  change PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (tprod K v₁) (tprod K v₂))) = _
  have hinter := interchange_tprod (K := K) v₁ v₂
  refine (congrArg
    (fun z => PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s)) z)) hinter).trans ?_
  have hinner :
      PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (tprod K (fun i => v₁ i ⊗ₜ[K] v₂ i)) =
        tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s)) :=
    PiTensorProduct.map_tprod _ _
  calc
    _ = PiTensorProduct.map (cwSquareTargetBasisMap K q W σ output)
        (tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) := congrArg _ hinner
    _ = tprod K (fun s =>
        cwSquareTargetBasisMap K q W σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      PiTensorProduct.map_tprod _ _
    _ = _ := by
      congr 1
      funext s
      dsimp [v₁, v₂]
      have hbasis := (cwSquareBasis_apply K q s
        (cwTermTriple q t s) (cwTermTriple q u s)).symm
      refine (congrArg
        (fun z => cwSquareTargetBasisMap K q W σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s) z)) hbasis).trans ?_
      exact cwSquareTargetBasisMap_apply_blockProj_basis
        K q W σ output s _

private noncomputable def cwCoupledVec
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    ∀ s : Fin 3, CoupledSpace K q s
  | ⟨0, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)
  | ⟨1, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)
  | ⟨2, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K)

private noncomputable def cwCoupledMonom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (CoupledSpace K q) :=
  tprod K (cwCoupledVec K q x y z)

/- The 112 classification is an independent child; retain only the common
four-sum expansion below. -/
/-
private noncomputable def cwCoupled112BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) : CoupledSpace K q s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)
  | ⟨2, _⟩ =>
      (if ab = (cwT q, cwO q) then
        (Pi.single (Sum.inl (0 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (if ab = (cwO q, cwT q) then
        (Pi.single (Sum.inl (1 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          (Pi.single (Sum.inr (j, i)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K)
        else 0)

private noncomputable def cwCoupled112ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q → PiTensorProduct K (CoupledSpace K q)
  | Sum.inr ⟨0, _⟩, Sum.inl (i, ⟨2, _⟩) =>
      cwCoupledMonom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)
  | Sum.inl (i, ⟨2, _⟩), Sum.inr ⟨0, _⟩ =>
      cwCoupledMonom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
  | Sum.inl (i, ⟨0, _⟩), Sum.inl (k, ⟨1, _⟩) =>
      cwCoupledMonom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))
  | Sum.inl (k, ⟨1, _⟩), Sum.inl (i, ⟨0, _⟩) =>
      cwCoupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))
  | _, _ => 0

private theorem cwCoupled112_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (0 : Fin 3) ∧ u = Sum.inl (i, (2 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (2 : Fin 3)) ∧ u = Sum.inr (0 : Fin 3)) ∨
    (∃ i k : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inl (k, (1 : Fin 3))) ∨
    (∃ k i : Fin q,
      t = Sum.inl (k, (1 : Fin 3)) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 2 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCoupled112ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 1 1 2 s) :
    cwCoupled112ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCoupled112ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

theorem cwSquare112_sum_sum_ite_eq_coord
    {β γ A : Type*} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [AddCommMonoid A]
    (i : β) (j : γ) (v : β → γ → A) :
    (∑ x : β, ∑ y : γ, if i = x ∧ j = y then v x y else 0) = v i j := by
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro y hy
      simp [Ne.symm hy]
  · intro x hx
    apply Fintype.sum_eq_zero
    intro y
    simp [Ne.symm hx]

private theorem cwCoupled112_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 1 1 2 s then
        cwCoupled112BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCoupled112ExpectedTermPair K q t u := by
  rcases cwCoupled112_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ |
    ⟨i, k, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCoupled112ExpectedTermPair, cwCoupledMonom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled112BasisOut, cwCoupledVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled112ExpectedTermPair, cwCoupledMonom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled112BasisOut, cwCoupledVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled112ExpectedTermPair, cwCoupledMonom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled112BasisOut, cwCoupledVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (cwSquare112_sum_sum_ite_eq_coord i k (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · simp only [cwCoupled112ExpectedTermPair, cwCoupledMonom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled112BasisOut, cwCoupledVec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (cwSquare112_sum_sum_ite_eq_coord k i (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · rw [cwCoupled112ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCoupled112ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCoupled112ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

-/

private theorem coupledTensor_eq_cwCoupledMonom_sums
    (K : Type u) [Field K] (q : ℕ) :
    coupledTensor K q =
      (∑ i : Fin q,
        cwCoupledMonom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q,
        cwCoupledMonom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupledMonom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rfl

/- The 112 restriction, cyclic bridge, and 211 restriction are independent
children. -/
/-
private theorem cwCoupled_cross_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupledMonom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupledMonom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled_fourth_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ k : Fin q, ∑ i : Fin q,
      cwCoupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupledMonom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled112_all_filtered_term_pairs_eq_coupledTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 1 1 2 s then
          cwCoupled112BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = coupledTensor K q := by
  simp_rw [cwCoupled112_filtered_term_pair_classification]
  rw [Fintype.sum_sum_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp [cwCoupled112ExpectedTermPair, Fin.sum_univ_succ]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_add_distrib]
  rw [cwCoupled_cross_swapped K q]
  rw [cwCoupled_fourth_swapped K q]
  rw [coupledTensor_eq_cwCoupledMonom_sums]
  ac_rfl

private theorem cwSquareCanonical_coupled112
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (coupledObj K q)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 1 2)) := by
  let maps := cwSquareTargetBasisMap K q (CoupledSpace K q)
    (cwSquareBlockType 1 1 2) (cwCoupled112BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 1 1 2)) = coupledTensor K q
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareTargetBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCoupled112_all_filtered_term_pairs_eq_coupledTensor K q

-/

/- The cyclic bridge and 211 restriction belong to the 211 child. -/
private theorem cyclicSymmetrization_eq_publicKron
    {K : Type u} [Field K] (X : TensorObj K 3) :
    cyclicSymmetrization X =
      TensorObj.kron X
        (TensorObj.kron (TensorObj.permObj cyclicPerm X)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) X)) := by
  unfold cyclicSymmetrization
  congr 3 <;> apply Equiv.ext <;> intro i <;> fin_cases i <;> rfl

private noncomputable def cwCoupled211Vec
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    ∀ s : Fin 3, (TensorObj.permObj cyclicPerm (coupledObj K q)).V s
  | ⟨0, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K)
  | ⟨1, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)
  | ⟨2, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)

private noncomputable def cwCoupled211Monom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K (TensorObj.permObj cyclicPerm (coupledObj K q)).V :=
  tprod K (cwCoupled211Vec K q x y z)

private theorem reindex_cwCoupledMonom_cyclic
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (cwCoupledMonom K q x y z) = cwCoupled211Monom K q x y z := by
  unfold cwCoupledMonom cwCoupled211Monom
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem permCoupled211Tensor_eq_cwCoupledMonom_sums
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.permObj cyclicPerm (coupledObj K q)).t =
      (∑ i : Fin q,
        cwCoupled211Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  change (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
      (coupledTensor K q) = _
  rw [coupledTensor_eq_cwCoupledMonom_sums]
  simp only [map_add, map_sum, reindex_cwCoupledMonom_cyclic]
  rfl

private noncomputable def cwCoupled211BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (TensorObj.permObj cyclicPerm (coupledObj K q)).V s :=
  match s with
  | ⟨0, _⟩ =>
      (if ab = (cwT q, cwO q) then
        (Pi.single (Sum.inl (0 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (if ab = (cwO q, cwT q) then
        (Pi.single (Sum.inl (1 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          (Pi.single (Sum.inr (j, i)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K)
        else 0)
  | ⟨1, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)

private noncomputable def cwCoupled211ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K (TensorObj.permObj cyclicPerm (coupledObj K q)).V
  | Sum.inr ⟨2, _⟩, Sum.inl (i, ⟨0, _⟩) =>
      cwCoupled211Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)
  | Sum.inl (i, ⟨0, _⟩), Sum.inr ⟨2, _⟩ =>
      cwCoupled211Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
  | Sum.inl (i, ⟨1, _⟩), Sum.inl (k, ⟨2, _⟩) =>
      cwCoupled211Monom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))
  | Sum.inl (k, ⟨2, _⟩), Sum.inl (i, ⟨1, _⟩) =>
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))
  | _, _ => 0

private theorem cwCoupled211_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (2 : Fin 3) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inr (2 : Fin 3)) ∨
    (∃ i k : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inl (k, (2 : Fin 3))) ∨
    (∃ k i : Fin q,
      t = Sum.inl (k, (2 : Fin 3)) ∧ u = Sum.inl (i, (1 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 2 1 1 s) :
    cwCoupled211ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCoupled211ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

theorem cwSquare211_sum_sum_ite_eq_coord
    {β γ A : Type*} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [AddCommMonoid A]
    (i : β) (j : γ) (v : β → γ → A) :
    (∑ x : β, ∑ y : γ, if i = x ∧ j = y then v x y else 0) = v i j := by
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro y hy
      simp [Ne.symm hy]
  · intro x hx
    apply Fintype.sum_eq_zero
    intro y
    simp [Ne.symm hx]

private theorem cwCoupled211_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 2 1 1 s then
        cwCoupled211BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCoupled211ExpectedTermPair K q t u := by
  rcases cwCoupled211_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ |
    ⟨i, k, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (cwSquare211_sum_sum_ite_eq_coord i k (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · simp only [cwCoupled211ExpectedTermPair, cwCoupled211Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled211BasisOut, cwCoupled211Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (cwSquare211_sum_sum_ite_eq_coord k i (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCoupled211ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCoupled211_cross_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inl k) (Sum.inr i) (Sum.inr (k, i))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled211_fourth_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ k : Fin q, ∑ i : Fin q,
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled211Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled211_all_filtered_term_pairs_eq_permTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 2 1 1 s then
          cwCoupled211BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) = (TensorObj.permObj cyclicPerm (coupledObj K q)).t := by
  calc
    _ = ∑ t : CWTerm q, ∑ u : CWTerm q,
        cwCoupled211ExpectedTermPair K q t u := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact cwCoupled211_filtered_term_pair_classification K q t u
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp_rw [Fintype.sum_sum_type]
      rw [Fintype.sum_prod_type]
      simp_rw [Fintype.sum_prod_type]
      simp [cwCoupled211ExpectedTermPair, Fin.sum_univ_succ]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      rw [cwCoupled211_cross_swapped K q]
      rw [cwCoupled211_fourth_swapped K q]
      change _ = (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (coupledTensor K q)
      rw [show (PiTensorProduct.reindex K (CoupledSpace K q) cyclicPerm)
        (coupledTensor K q) = _ from
          permCoupled211Tensor_eq_cwCoupledMonom_sums K q]
      ac_rfl

private theorem cwSquareCanonical_coupled211
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict (TensorObj.permObj cyclicPerm (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 1 1)) := by
  let maps := cwSquareTargetBasisMap K q
    (TensorObj.permObj cyclicPerm (coupledObj K q)).V
    (cwSquareBlockType 2 1 1) (cwCoupled211BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 2 1 1)) =
      (TensorObj.permObj cyclicPerm (coupledObj K q)).t
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareTargetBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCoupled211_all_filtered_term_pairs_eq_permTensor K q

/- The 121 restriction is an independent child. -/
/-
private noncomputable def cwCoupled121Vec
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    ∀ s : Fin 3,
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V s
  | ⟨0, _⟩ => (Pi.single y 1 : (Fin q ⊕ Fin q) → K)
  | ⟨1, _⟩ => (Pi.single z 1 : (Fin 2 ⊕ (Fin q × Fin q)) → K)
  | ⟨2, _⟩ => (Pi.single x 1 : (Fin q ⊕ Fin q) → K)

private noncomputable def cwCoupled121Monom
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    PiTensorProduct K
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V :=
  tprod K (cwCoupled121Vec K q x y z)

private theorem reindex_cwCoupledMonom_cyclic_sq
    (K : Type u) [Field K] (q : ℕ)
    (x y : Fin q ⊕ Fin q) (z : Fin 2 ⊕ (Fin q × Fin q)) :
    (PiTensorProduct.reindex K (CoupledSpace K q)
        (cyclicPerm.trans cyclicPerm))
        (cwCoupledMonom K q x y z) = cwCoupled121Monom K q x y z := by
  unfold cwCoupledMonom cwCoupled121Monom
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem permCoupled121Tensor_eq_cwCoupledMonom_sums
    (K : Type u) [Field K] (q : ℕ) :
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).t =
      (∑ i : Fin q,
        cwCoupled121Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)) +
      (∑ k : Fin q,
        cwCoupled121Monom K q (Sum.inr k) (Sum.inr k) (Sum.inl 1)) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled121Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) +
      (∑ i : Fin q, ∑ k : Fin q,
        cwCoupled121Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  change (PiTensorProduct.reindex K (CoupledSpace K q)
      (cyclicPerm.trans cyclicPerm)) (coupledTensor K q) = _
  rw [coupledTensor_eq_cwCoupledMonom_sums]
  simp only [map_add, map_sum, reindex_cwCoupledMonom_cyclic_sq]
  rfl

private noncomputable def cwCoupled121BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V s :=
  match s with
  | ⟨0, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)
  | ⟨1, _⟩ =>
      (if ab = (cwT q, cwO q) then
        (Pi.single (Sum.inl (0 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (if ab = (cwO q, cwT q) then
        (Pi.single (Sum.inl (1 : Fin 2)) 1 :
          (Fin 2 ⊕ (Fin q × Fin q)) → K)
      else 0) +
      (∑ i : Fin q, ∑ j : Fin q,
        if ab = (cwM q i, cwM q j) then
          (Pi.single (Sum.inr (j, i)) 1 :
            (Fin 2 ⊕ (Fin q × Fin q)) → K)
        else 0)
  | ⟨2, _⟩ =>
      (∑ i : Fin q,
        if ab = (cwO q, cwM q i) then
          (Pi.single (Sum.inl i) 1 : (Fin q ⊕ Fin q) → K)
        else 0) +
      (∑ i : Fin q,
        if ab = (cwM q i, cwO q) then
          (Pi.single (Sum.inr i) 1 : (Fin q ⊕ Fin q) → K)
        else 0)

private noncomputable def cwCoupled121ExpectedTermPair
    (K : Type u) [Field K] (q : ℕ) :
    CWTerm q → CWTerm q →
      PiTensorProduct K
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V
  | Sum.inr ⟨1, _⟩, Sum.inl (i, ⟨1, _⟩) =>
      cwCoupled121Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)
  | Sum.inl (i, ⟨1, _⟩), Sum.inr ⟨1, _⟩ =>
      cwCoupled121Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
  | Sum.inl (i, ⟨0, _⟩), Sum.inl (k, ⟨2, _⟩) =>
      cwCoupled121Monom K q (Sum.inr i) (Sum.inl k) (Sum.inr (k, i))
  | Sum.inl (k, ⟨2, _⟩), Sum.inl (i, ⟨0, _⟩) =>
      cwCoupled121Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))
  | _, _ => 0

private noncomputable def cwCoupled121ExpectedTermPairDelta
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    PiTensorProduct K
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V :=
  (∑ i : Fin q,
    if t = Sum.inr (1 : Fin 3) ∧ u = Sum.inl (i, (1 : Fin 3)) then
      cwCoupled121Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0)
    else 0) +
  (∑ i : Fin q,
    if t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inr (1 : Fin 3) then
      cwCoupled121Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
    else 0) +
  (∑ p : Fin q × Fin q,
    if t = Sum.inl (p.1, (0 : Fin 3)) ∧
        u = Sum.inl (p.2, (2 : Fin 3)) then
      cwCoupled121Monom K q (Sum.inr p.1) (Sum.inl p.2)
        (Sum.inr (p.2, p.1))
    else 0) +
  (∑ p : Fin q × Fin q,
    if t = Sum.inl (p.1, (2 : Fin 3)) ∧
        u = Sum.inl (p.2, (0 : Fin 3)) then
      cwCoupled121Monom K q (Sum.inl p.2) (Sum.inr p.1)
        (Sum.inr (p.2, p.1))
    else 0)

private theorem sum_ite_eq_coord {β A : Type*} [Fintype β] [DecidableEq β]
    [AddCommMonoid A] (i : β) (v : β → A) :
    (∑ x : β, if i = x then v x else 0) = v i := by
  rw [Fintype.sum_eq_single i]
  · simp
  · intro x hx
    simp [Ne.symm hx]

private theorem sum_ite_eq_prod_coord {β γ A : Type*}
    [Fintype β] [DecidableEq β] [Fintype γ] [DecidableEq γ]
    [AddCommMonoid A] (i : β) (j : γ) (v : β × γ → A) :
    (∑ x : β × γ, if i = x.1 ∧ j = x.2 then v x else 0) = v (i, j) := by
  simpa [Prod.ext_iff] using sum_ite_eq_coord (i, j) v

private theorem cwCoupled121_delta_first_eval
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    (∑ x : Fin q, if i = x then
      cwCoupled121Monom K q (Sum.inl x) (Sum.inl x) (Sum.inl 0)
    else 0) =
      cwCoupled121Monom K q (Sum.inl i) (Sum.inl i) (Sum.inl 0) := by
  simpa using sum_ite_eq_coord i (fun x : Fin q =>
    cwCoupled121Monom K q (Sum.inl x) (Sum.inl x) (Sum.inl 0))

private theorem cwCoupled121_delta_second_eval
    (K : Type u) [Field K] (q : ℕ) (i : Fin q) :
    (∑ x : Fin q, if i = x then
      cwCoupled121Monom K q (Sum.inr x) (Sum.inr x) (Sum.inl 1)
    else 0) =
      cwCoupled121Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1) := by
  simpa using sum_ite_eq_coord i (fun x : Fin q =>
    cwCoupled121Monom K q (Sum.inr x) (Sum.inr x) (Sum.inl 1))

private theorem cwCoupled121_delta_third_eval
    (K : Type u) [Field K] (q : ℕ) (i j : Fin q) :
    (∑ x : Fin q × Fin q, if i = x.1 ∧ j = x.2 then
      cwCoupled121Monom K q (Sum.inl x.2) (Sum.inr x.1)
        (Sum.inr (x.2, x.1))
    else 0) =
      cwCoupled121Monom K q (Sum.inl j) (Sum.inr i) (Sum.inr (j, i)) := by
  simpa using sum_ite_eq_prod_coord i j (fun x : Fin q × Fin q =>
    cwCoupled121Monom K q (Sum.inl x.2) (Sum.inr x.1)
      (Sum.inr (x.2, x.1)))

private theorem cwCoupled121_delta_fourth_eval
    (K : Type u) [Field K] (q : ℕ) (i j : Fin q) :
    (∑ x : Fin q × Fin q, if i = x.1 ∧ j = x.2 then
      cwCoupled121Monom K q (Sum.inr x.1) (Sum.inl x.2)
        (Sum.inr (x.2, x.1))
    else 0) =
      cwCoupled121Monom K q (Sum.inr i) (Sum.inl j) (Sum.inr (j, i)) := by
  simpa using sum_ite_eq_prod_coord i j (fun x : Fin q × Fin q =>
    cwCoupled121Monom K q (Sum.inr x.1) (Sum.inl x.2)
      (Sum.inr (x.2, x.1)))

private theorem cwCoupled121ExpectedTermPair_eq_delta
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    cwCoupled121ExpectedTermPair K q t u =
      cwCoupled121ExpectedTermPairDelta K q t u := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwCoupled121ExpectedTermPair,
      cwCoupled121ExpectedTermPairDelta, sum_ite_eq_coord,
      sum_ite_eq_prod_coord, cwCoupled121_delta_first_eval,
      cwCoupled121_delta_second_eval, cwCoupled121_delta_third_eval,
      cwCoupled121_delta_fourth_eval] <;> abel
  case inl.inl.«0».«2» =>
    rw [Fintype.sum_eq_single (i, j)]
    · simp only [true_and, if_true]
      change cwCoupled121Monom K q (Sum.inr i) (Sum.inl j)
          (Sum.inr (j, i)) =
        (0 : PiTensorProduct K
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K q)).V) +
          cwCoupled121Monom K q (Sum.inr i) (Sum.inl j)
            (Sum.inr (j, i))
      exact (zero_add _).symm
    · intro x hx
      have hne : ¬ (i = x.1 ∧ j = x.2) := by
        intro h
        apply hx
        exact Prod.ext h.1.symm h.2.symm
      simp [hne]
      change (0 : PiTensorProduct K
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K q)).V) = 0
      rfl
  case inl.inl.«2».«0» =>
    rw [Fintype.sum_eq_single (i, j)]
    · simp only [true_and, if_true]
      change cwCoupled121Monom K q (Sum.inl j) (Sum.inr i)
          (Sum.inr (j, i)) =
        (0 : PiTensorProduct K
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K q)).V) +
          cwCoupled121Monom K q (Sum.inl j) (Sum.inr i)
            (Sum.inr (j, i))
      exact (zero_add _).symm
    · intro x hx
      have hne : ¬ (i = x.1 ∧ j = x.2) := by
        intro h
        apply hx
        exact Prod.ext h.1.symm h.2.symm
      simp [hne]
      change (0 : PiTensorProduct K
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K q)).V) = 0
      rfl
  case inl.inr.«1».«1» =>
    rw [Fintype.sum_eq_single i]
    · simp only [if_pos rfl]
      change cwCoupled121Monom K q (Sum.inr i) (Sum.inr i)
          (Sum.inl 1) =
        (0 : PiTensorProduct K
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (coupledObj K q)).V) +
          cwCoupled121Monom K q (Sum.inr i) (Sum.inr i) (Sum.inl 1)
      exact (zero_add _).symm
    · intro x hx
      simp [Ne.symm hx]
      change (0 : PiTensorProduct K
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K q)).V) = 0
      rfl
  case inr.inl.«1».«1» =>
    rw [Fintype.sum_eq_single j]
    · simp only [if_pos rfl]
      change cwCoupled121Monom K q (Sum.inl j) (Sum.inl j)
          (Sum.inl 0) =
        cwCoupled121Monom K q (Sum.inl j) (Sum.inl j) (Sum.inl 0) +
          (0 : PiTensorProduct K
            (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K q)).V)
      exact (add_zero _).symm
    · intro x hx
      simp [Ne.symm hx]
      change (0 : PiTensorProduct K
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K q)).V) = 0
      rfl

private theorem cwCoupled121_special_or_grade_mismatch
    (q : ℕ) (t u : CWTerm q) :
    (∃ i : Fin q,
      t = Sum.inr (1 : Fin 3) ∧ u = Sum.inl (i, (1 : Fin 3))) ∨
    (∃ i : Fin q,
      t = Sum.inl (i, (1 : Fin 3)) ∧ u = Sum.inr (1 : Fin 3)) ∨
    (∃ i k : Fin q,
      t = Sum.inl (i, (0 : Fin 3)) ∧ u = Sum.inl (k, (2 : Fin 3))) ∨
    (∃ k i : Fin q,
      t = Sum.inl (k, (2 : Fin 3)) ∧ u = Sum.inl (i, (0 : Fin 3))) ∨
    cwSquarePairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 1 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 2 ∨
    cwSquarePairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwSquarePairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwCoupled121ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 1 2 1 s) :
    cwCoupled121ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCoupled121ExpectedTermPair, cwSquarePairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem sum_sum_ite_eq_coord
    {β γ A : Type*} [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [AddCommMonoid A]
    (i : β) (j : γ) (v : β → γ → A) :
    (∑ x : β, ∑ y : γ, if i = x ∧ j = y then v x y else 0) = v i j := by
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp
    · intro y hy
      simp [Ne.symm hy]
  · intro x hx
    apply Fintype.sum_eq_zero
    intro y
    simp [Ne.symm hx]

private theorem cwCoupled121_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
          cwSquareBlockType 1 2 1 s then
        cwCoupled121BasisOut K q s
          (cwRectTermTriple q t s, cwRectTermTriple q u s)
      else 0) = cwCoupled121ExpectedTermPair K q t u := by
  rcases cwCoupled121_special_or_grade_mismatch q t u with
    ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩ |
    ⟨i, k, rfl, rfl⟩ | ⟨k, i, rfl, rfl⟩ | h0 | h1 | h2
  · simp only [cwCoupled121ExpectedTermPair, cwCoupled121Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled121BasisOut, cwCoupled121Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled121ExpectedTermPair, cwCoupled121Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled121BasisOut, cwCoupled121Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT]
  · simp only [cwCoupled121ExpectedTermPair, cwCoupled121Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled121BasisOut, cwCoupled121Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (sum_sum_ite_eq_coord i k (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · simp only [cwCoupled121ExpectedTermPair, cwCoupled121Monom]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCoupled121BasisOut, cwCoupled121Vec,
        cwSquarePairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwSquareBlockType, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]
    exact (sum_sum_ite_eq_coord k i (fun x x_1 =>
      (Pi.single (Sum.inr (x_1, x)) 1 :
        (Fin 2 ⊕ (Fin q × Fin q)) → K))).symm
  · rw [cwCoupled121ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 0 (by simpa [cwSquareBlockType] using h0)]
    apply (PiTensorProduct.tprod K).map_coord_zero (0 : Fin 3)
    simp [h0, cwSquareBlockType]
  · rw [cwCoupled121ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 1 (by simpa [cwSquareBlockType] using h1)]
    apply (PiTensorProduct.tprod K).map_coord_zero (1 : Fin 3)
    simp [h1, cwSquareBlockType]
  · rw [cwCoupled121ExpectedTermPair_eq_zero_of_grade_mismatch
      K q t u 2 (by simpa [cwSquareBlockType] using h2)]
    apply (PiTensorProduct.tprod K).map_coord_zero (2 : Fin 3)
    simp [h2, cwSquareBlockType]

private theorem cwCoupled121_third_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ k : Fin q, ∑ i : Fin q,
      cwCoupled121Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled121Monom K q (Sum.inl i) (Sum.inr k) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled121_fourth_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ k : Fin q, ∑ i : Fin q,
      cwCoupled121Monom K q (Sum.inr i) (Sum.inl k) (Sum.inr (k, i))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled121Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem cwCoupled121_fourth_delta_swapped
    (K : Type u) [Field K] (q : ℕ) :
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled121Monom K q (Sum.inr i) (Sum.inl k) (Sum.inr (k, i))) =
    (∑ i : Fin q, ∑ k : Fin q,
      cwCoupled121Monom K q (Sum.inr k) (Sum.inl i) (Sum.inr (i, k))) := by
  rw [Finset.sum_comm]

private theorem sum_fin_three {A : Type*} [AddCommMonoid A]
    (f : Fin 3 → A) :
    (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp [add_assoc]

private theorem sum_pair_indexed_delta
    {α β A : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [AddCommMonoid A] (a b : β → α) (v : β → A) :
    (∑ t : α, ∑ u : α, ∑ i : β,
      if t = a i ∧ u = b i then v i else 0) = ∑ i : β, v i := by
  classical
  calc
    _ = ∑ t : α, ∑ i : β, ∑ u : α,
        if t = a i ∧ u = b i then v i else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_comm]
    _ = ∑ i : β, ∑ t : α, ∑ u : α,
        if t = a i ∧ u = b i then v i else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Fintype.sum_eq_single (a i)]
      · rw [Fintype.sum_eq_single (b i)]
        · simp
        · intro u hu
          simp [hu]
      · intro t ht
        apply Fintype.sum_eq_zero
        intro u
        simp [ht]

private theorem cwCoupled121_all_filtered_term_pairs_eq_permTensor
    (K : Type u) [Field K] (q : ℕ) :
    (∑ t : CWTerm q, ∑ u : CWTerm q,
      tprod K (fun s =>
        if cwSquarePairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
            cwSquareBlockType 1 2 1 s then
          cwCoupled121BasisOut K q s
            (cwRectTermTriple q t s, cwRectTermTriple q u s)
        else 0)) =
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).t := by
  calc
    _ = ∑ t : CWTerm q, ∑ u : CWTerm q,
        cwCoupled121ExpectedTermPair K q t u := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact cwCoupled121_filtered_term_pair_classification K q t u
    _ = ∑ t : CWTerm q, ∑ u : CWTerm q,
        cwCoupled121ExpectedTermPairDelta K q t u := by
      apply Finset.sum_congr rfl
      intro t ht
      apply Finset.sum_congr rfl
      intro u hu
      exact cwCoupled121ExpectedTermPair_eq_delta K q t u
    _ = _ := by
      simp only [cwCoupled121ExpectedTermPairDelta,
        Finset.sum_add_distrib]
      rw [sum_pair_indexed_delta]
      rw [sum_pair_indexed_delta]
      rw [sum_pair_indexed_delta]
      rw [sum_pair_indexed_delta]
      rw [Fintype.sum_prod_type]
      rw [Fintype.sum_prod_type]
      simp only [Prod.fst, Prod.snd]
      rw [cwCoupled121_third_swapped K q]
      rw [cwCoupled121_fourth_delta_swapped K q]
      change _ = (PiTensorProduct.reindex K (CoupledSpace K q)
        (cyclicPerm.trans cyclicPerm)) (coupledTensor K q)
      rw [show (PiTensorProduct.reindex K (CoupledSpace K q)
        (cyclicPerm.trans cyclicPerm)) (coupledTensor K q) = _ from
          permCoupled121Tensor_eq_cwCoupledMonom_sums K q]
      ac_rfl

private theorem cwSquareCanonical_coupled121
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 2 1)) := by
  let maps := cwSquareTargetBasisMap K q
    (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).V
    (cwSquareBlockType 1 2 1) (cwCoupled121BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 1 2 1)) =
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q)).t
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareTargetBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCoupled121_all_filtered_term_pairs_eq_permTensor K q

-/

/- The cyclic assembly and full certificate wrapper live in the parent. -/
/-
private theorem cwSquareCanonical_restrict_kron
    {K : Type u} [Field K] {X X' Y Y' : TensorObj K 3}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  let P := TensorQ.tensorStrassen K 3 (by norm_num)
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  have hxl := P.mul_right _ _ hx (TensorQ.toQ Y)
  have hyl := P.mul_right _ _ hy (TensorQ.toQ X')
  have hmul : P.le (TensorQ.toQ X * TensorQ.toQ Y)
      (TensorQ.toQ X' * TensorQ.toQ Y') := by
    exact P.le_trans _ _ _ hxl (by simpa [mul_comm] using hyl)
  exact hmul

private theorem cwSquareCanonical_coupledCyclic
    (K : Type u) [Field K] (q : ℕ) :
    TensorObj.Restrict
      (cyclicSymmetrization (coupledObj K q))
      (TensorObj.kron
        ((cwSquareCanonicalGrading K q).blockSubtensor
          (cwSquareBlockType 1 1 2))
        (TensorObj.kron
          ((cwSquareCanonicalGrading K q).blockSubtensor
            (cwSquareBlockType 2 1 1))
          ((cwSquareCanonicalGrading K q).blockSubtensor
            (cwSquareBlockType 1 2 1)))) := by
  rw [cyclicSymmetrization_eq_publicKron]
  exact cwSquareCanonical_restrict_kron
    (cwSquareCanonical_coupled112 K q)
    (cwSquareCanonical_restrict_kron
      (cwSquareCanonical_coupled211 K q)
      (cwSquareCanonical_coupled121 K q))

theorem cwSquareCanonical_certificate
    (K : Type u) [Field K] (q : ℕ) :
    Nonempty (CWSquareFiveGradeCertificate K q) := by
  exact ⟨{
    grading := cwSquareCanonicalGrading K q
    support := cwSquareCanonical_support K q
    scalar004 := cwSquareCanonical_scalar004 K q
    scalar040 := cwSquareCanonical_scalar040 K q
    scalar400 := cwSquareCanonical_scalar400 K q
    rect013 := cwSquareCanonical_rect013 K q
    rect031 := cwSquareCanonical_rect031 K q
    rect103 := cwSquareCanonical_rect103 K q
    rect301 := cwSquareCanonical_rect301 K q
    rect130 := cwSquareCanonical_rect130 K q
    rect310 := cwSquareCanonical_rect310 K q
    central022 := cwSquareCanonical_central022 K q
    central202 := cwSquareCanonical_central202 K q
    central220 := cwSquareCanonical_central220 K q
    coupled112 := cwSquareCanonical_coupled112 K q
    coupledCyclic := cwSquareCanonical_coupledCyclic K q
  }⟩

/- A direct equality statement is ill-typed because mode families are dependent;
the cyclic transport must be bundled by explicit modewise linear maps. -/
/-
private theorem cwSquareCanonical_decomp_mode_eq
    (K : Type u) [Field K] (q : ℕ) (s r : Fin 3) (a : Fin 5) :
    (cwSquareCanonicalGrading K q).decomp s a =
      (cwSquareCanonicalGrading K q).decomp r a := by
  fin_cases s <;> fin_cases r <;> rfl

private theorem reindex_CWMonom_cyclic
    (K : Type u) [Field K] (q : ℕ) (a b c : Fin (q + 2)) :
    (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWMonom K q a b c) = CWMonom K q c a b := by
  unfold CWMonom
  rw [PiTensorProduct.reindex_tprod]
  congr 1
  funext s
  fin_cases s <;> rfl

private theorem reindex_CWTensor_cyclic
    (K : Type u) [Field K] (q : ℕ) :
    (PiTensorProduct.reindex K (CWSpace K q) cyclicPerm)
        (CWTensor K q) = CWTensor K q := by
  unfold CWTensor
  simp only [map_add, map_sum, reindex_CWMonom_cyclic]
  abel
-/

end CWSquareCanonical

end MME

-/

open MME

theorem mme_CW_square_q6_five_grade_orbit_certificate
    {K : Type u} [Field K] :
    Nonempty (CWSquareFiveGradeCertificate K 6) := by
  exact cwSquareCanonical_certificate K 6

theorem solution
    {K : Type u} [Field K] :
    Nonempty (CWSquareFiveGradeCertificate K 6) := by
  exact cwSquareCanonical_certificate K 6
-/

end CWSquareCanonical

end MME

open MME

universe u

/- Elementary child entry point. -/
/-
/- Superseded coupled-211 entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 0 3)) ∧
    TensorObj.Restrict (MMObj K (2 * q) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 0 1)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 3 0)) ∧
    TensorObj.Restrict (MMObj K 1 (2 * q) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 3 1 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 (q ^ 2 + 2))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)) ∧
    TensorObj.Restrict (MMObj K (q ^ 2 + 2) 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)) ∧
    TensorObj.Restrict (MMObj K 1 (q ^ 2 + 2) 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 2 0)) := by
  exact ⟨
    cwSquareCanonical_support K q,
    cwSquareCanonical_scalar004 K q,
    cwSquareCanonical_scalar040 K q,
    cwSquareCanonical_scalar400 K q,
    cwSquareCanonical_rect013 K q,
    cwSquareCanonical_rect031 K q,
    cwSquareCanonical_rect103 K q,
    cwSquareCanonical_rect301 K q,
    cwSquareCanonical_rect130 K q,
    cwSquareCanonical_rect310 K q,
    cwSquareCanonical_central022 K q,
    cwSquareCanonical_central202 K q,
    cwSquareCanonical_central220 K q⟩

-/

/- Coupled-121 child entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 2 1)) := by
  exact cwSquareCanonical_coupled121 K q

-/

/- Coupled-112 child entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (coupledObj K q)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 1 2)) := by
  exact cwSquareCanonical_coupled112 K q

-/

/- Coupled-211 child entry point. -/
/-
/- Final coupled-211 upload entry point, now superseded. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 1 1)) := by
  exact cwSquareCanonical_coupled211 K q
-/

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) := by
  exact ⟨cwSquareCanonical_support K q,
    cwSquareCanonical_scalar004 K q,
    cwSquareCanonical_scalar040 K q,
    cwSquareCanonical_scalar400 K q⟩

-/

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    (∀ I J L : Fin 5, I.val + J.val + L.val ≠ 4 →
      (cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType I J L) = 0) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 0 4)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 4 0)) ∧
    TensorObj.Restrict (MMObj K 1 1 1)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 4 0 0)) := by
  exact ⟨cwSquareCanonical_support K q,
    cwSquareCanonical_scalar004 K q,
    cwSquareCanonical_scalar040 K q,
    cwSquareCanonical_scalar400 K q⟩

-/

/- Coupled-112 retry entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (coupledObj K q)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 1 2)) := by
  exact cwSquareCanonical_coupled112 K q

-/

/- Coupled-121 retry entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 2 1)) := by
  exact cwSquareCanonical_coupled121 K q

-/

/- Coupled-112 post-inline entry point. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (coupledObj K q)
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 1 1 2)) := by
  exact cwSquareCanonical_coupled112 K q

-/

/- Coupled-211 post-inline upload entry point, superseded. -/
/-
theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (TensorObj.permObj cyclicPerm (coupledObj K q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 1 1)) := by
  exact cwSquareCanonical_coupled211 K q
-/

theorem solution
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 1 3)) ∧
    TensorObj.Restrict (MMObj K 1 1 (2 * q))
      ((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 3 1)) := by
  exact ⟨cwSquareCanonical_rect013 K q, cwSquareCanonical_rect031 K q⟩
