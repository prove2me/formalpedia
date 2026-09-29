-- Prove2me | solution 1 for mme_dwz_q6_rect301_exact_z_basis_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:10:46.471838+00:00
-- url     : https://prove2.me/submissions/d7443764-1da6-438e-9208-a4bc531b32cd

import Definitions.Def_mme_CW_square_five_grade_certificate
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_permutation
import Definitions.Def_mme_dwz_component_word_projection
import Theorems.Thm_mme_dwz_coarseClassBasis_q6_val
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

open PiTensorProduct TensorProduct BigOperators DirectSum Module

namespace MME

universe u

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

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

private def cwCoordGrade (q : ℕ) (a : Fin (q + 2)) : Fin 3 :=
  if a.val = 0 then 0 else if a.val = q + 1 then 2 else 1

private def cwPairGrade (q : ℕ) (ab : Fin (q + 2) × Fin (q + 2)) : Fin 5 :=
  ⟨(cwCoordGrade q ab.1).val + (cwCoordGrade q ab.2).val, by omega⟩

private noncomputable def cwSquareBasis
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

/-- Public alias for the canonical basis used by the explicit source routers
in this file.  A separate compatibility leaf identifies it with the public
DWZ canonical basis. -/
noncomputable def cwSquareRouterBasis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :=
  cwSquareBasis K q s

/-- Public alias for the canonical grading used by the explicit source
routers in this file. -/
noncomputable def cwSquareRouterGrading
    (K : Type u) [Field K] (q : ℕ) :=
  cwSquareCanonicalGrading K q

private theorem cwSquareCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 5) (i j : Fin (q + 2)) :
    (cwSquareCanonicalGrading K q).blockProj s a
        (cwSquareBasis K q s (i, j)) =
      if h : cwPairGrade q (i, j) = a then
        ⟨cwSquareBasis K q s (i, j), by
          simpa [h] using
            basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j)⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K q) s (cwPairGrade q (i, j)) _
      (basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j))
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K q) s a (cwPairGrade q (i, j)) (Ne.symm h) _
      (basis_mem_basisGrade (cwSquareBasis K q s) (cwPairGrade q) (i, j))

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
    cwSquareBasis K q s (a, b) = cwVec K q s a ⊗ₜ[K] cwVec K q s b := by
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
  change (PiTensorProduct.lift interchangeOuter
      (PiTensorProduct.tprod K v)) (PiTensorProduct.tprod K w) = _
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

private theorem cwCoordGrade_O (q : ℕ) : cwCoordGrade q (cwO q) = 0 := by
  simp [cwCoordGrade, cwO]

private theorem cwCoordGrade_M (q : ℕ) (i : Fin q) :
    cwCoordGrade q (cwM q i) = 1 := by
  simp [cwCoordGrade, cwM]
  omega

private theorem cwCoordGrade_T (q : ℕ) : cwCoordGrade q (cwT q) = 2 := by
  simp [cwCoordGrade, cwT]

private theorem cwSupportedTriple_grade_sum_two
    (q : ℕ) (a b c : Fin (q + 2))
    (h : cwSupportedTriple q a b c) :
    (cwCoordGrade q a).val + (cwCoordGrade q b).val +
      (cwCoordGrade q c).val = 2 := by
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

private noncomputable def cwSquareBasisMap
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K]
      (MMObj K n m p).V s :=
  ((cwSquareBasis K q s).constr K (output s)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareBasisMap K q n m p σ output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareBasis K q s idx)) =
      if cwPairGrade q idx = σ s then output s idx else 0 := by
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
        if cwPairGrade q
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
    cwPairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 0 ∨
    cwPairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 1 ∨
    cwPairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 3 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwPairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect013ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwPairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 1 3 s) :
    cwRect013ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect013ExpectedTermPair, cwPairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect013_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
        cwRect013XVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect013ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect013BasisOut, cwRect013MMVec,
        cwRect013XVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
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
        if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
    cwPairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 0 ∨
    cwPairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 3 ∨
    cwPairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwPairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect031ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwPairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 3 1 s) :
    cwRect031ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect031ExpectedTermPair, cwPairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect031_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
        cwRect013XVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect031ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect031BasisOut, cwRect013MMVec,
        cwRect013XVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
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
        if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
    cwPairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 1 ∨
    cwPairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 0 ∨
    cwPairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 3 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwPairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect103ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwPairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 1 0 3 s) :
    cwRect103ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect103ExpectedTermPair, cwPairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect103_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
        cwRect103YVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect103ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect103BasisOut, cwRect103MMVec,
        cwRect103YVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
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
        if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
    cwPairGrade q (cwRectTermTriple q t 0, cwRectTermTriple q u 0) ≠ 3 ∨
    cwPairGrade q (cwRectTermTriple q t 1, cwRectTermTriple q u 1) ≠ 0 ∨
    cwPairGrade q (cwRectTermTriple q t 2, cwRectTermTriple q u 2) ≠ 1 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;>
    simp [cwRectTermTriple, cwPairGrade, cwCoordGrade_O,
      cwCoordGrade_M, cwCoordGrade_T]

private theorem cwRect301ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwPairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 3 0 1 s) :
    cwRect301ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwRect301ExpectedTermPair, cwPairGrade,
      cwCoordGrade_O, cwCoordGrade_M, cwCoordGrade_T,
      cwSquareBlockType] at hgrade ⊢

private theorem cwRect301_filtered_term_pair_classification
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) :
    tprod K (fun s =>
      if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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
        cwRect103YVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
        cwCoordGrade_T, cwSquareBlockType, cwM_eq_cwM_iff,
        cwO_ne_cwM, cwT_ne_cwM]
  · simp only [cwRect301ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwRect301BasisOut, cwRect103MMVec,
        cwRect103YVec, cwPairGrade, cwCoordGrade_O, cwCoordGrade_M,
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
        if cwPairGrade q (cwRectTermTriple q t s, cwRectTermTriple q u s) =
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

/-! ## Exact q=6 rectangular Z-basis router -/

open MME.DWZComponentRestriction

private theorem q6GradeThree_left (i : Fin 6) :
    cwSquarePairGrade 6 (cwT 6, cwM 6 i) = 3 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, cwT, cwM, hiT]

private theorem q6GradeThree_right (i : Fin 6) :
    cwSquarePairGrade 6 (cwM 6 i, cwT 6) = 3 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, cwT, cwM, hiT]

private def q6GradeThreeEncode : Fin 6 ⊕ Fin 6 → CoarsePair 6 3
  | Sum.inl i => ⟨(cwT 6, cwM 6 i), q6GradeThree_left i⟩
  | Sum.inr i => ⟨(cwM 6 i, cwT 6), q6GradeThree_right i⟩

private def q6GradeThreeDecode (p : CoarsePair 6 3) : Fin 6 ⊕ Fin 6 :=
  if p.1.1.val = 7 then
    Sum.inl (Fin.ofNat 6 (p.1.2.val - 1))
  else
    Sum.inr (Fin.ofNat 6 (p.1.1.val - 1))

private theorem q6GradeThreeDecode_encode :
    Function.LeftInverse q6GradeThreeDecode q6GradeThreeEncode := by
  intro c
  rcases c with i | i <;> fin_cases i <;> rfl

private theorem q6GradeThreeEncode_decode :
    Function.RightInverse q6GradeThreeDecode q6GradeThreeEncode := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [q6GradeThreeDecode, q6GradeThreeEncode, cwSquarePairGrade,
      cwSquareCoordGrade, cwM, cwT] at hp ⊢

private noncomputable def q6GradeThreeEquiv :
    CoarsePair 6 3 ≃ (Fin 6 ⊕ Fin 6) where
  toFun := q6GradeThreeDecode
  invFun := q6GradeThreeEncode
  left_inv := q6GradeThreeEncode_decode
  right_inv := q6GradeThreeDecode_encode

private noncomputable def q6GradeThreeCoordinate :
    LiftedCoarsePair.{u} 6 3 ≃ Fin 12 :=
  Equiv.ulift.trans <| q6GradeThreeEquiv.trans (cwRectChannelEquiv 6)

private theorem q6GradeThreeEquiv_source (p : CoarsePair 6 3) :
    p.1 =
      match q6GradeThreeEquiv p with
      | Sum.inl i => (cwT 6, cwM 6 i)
      | Sum.inr i => (cwM 6 i, cwT 6) := by
  have h := q6GradeThreeEquiv.symm_apply_apply p
  generalize hc : q6GradeThreeEquiv p = c at h ⊢
  rcases c with i | i <;>
    simpa [q6GradeThreeEquiv, q6GradeThreeEncode] using
      congrArg Subtype.val h.symm

private theorem q6GradeThreeCoordinate_eq_left
    (p : LiftedCoarsePair.{u} 6 3) (i : Fin 6)
    (h : q6GradeThreeEquiv p.down = Sum.inl i) :
    q6GradeThreeCoordinate p = cwRectLeft 6 i := by
  change cwRectChannelEquiv 6 (q6GradeThreeEquiv p.down) = _
  rw [h]
  exact cwRectChannelEquiv_inl 6 i

private theorem q6GradeThreeCoordinate_eq_right
    (p : LiftedCoarsePair.{u} 6 3) (i : Fin 6)
    (h : q6GradeThreeEquiv p.down = Sum.inr i) :
    q6GradeThreeCoordinate p = cwRectRight 6 i := by
  change cwRectChannelEquiv 6 (q6GradeThreeEquiv p.down) = _
  rw [h]
  exact cwRectChannelEquiv_inr 6 i

private noncomputable def q6GradeThreeZBasis
    (K : Type u) [Field K] :
    Basis (LiftedCoarsePair.{u} 6 3) K
      ((cwSquareCanonicalGrading K 6).classOf 2 3) :=
  (coarseClassBasis (K := K) 6 2 3).reindex Equiv.ulift.symm

private theorem q6GradeThreeZBasis_blockProj
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 3) :
    q6GradeThreeZBasis K p =
      (cwSquareCanonicalGrading K 6).blockProj 2 3
        (cwSquareBasis K 6 2 p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · have hr :
        q6GradeThreeZBasis K p =
          coarseClassBasis (K := K) 6 2 3 p.down := by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 3) Equiv.ulift.symm p
    rw [hr]
    exact mme_dwz_coarseClassBasis_q6_val K 2 3 p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

/-- The canonical q=6 `013` restriction can be chosen to route every named
coarse-grade-three Z basis vector to its literal standard channel in
`⟨1,1,12⟩`. -/
theorem cwSquareCanonical_rect013_q6_Z_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 0 1 3 s) →ₗ[K]
          (MMObj K 1 1 12).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 0 1 3)) =
        MMTensor K 1 1 12 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K) := by
  let maps := cwSquareBasisMap K 6 1 1 12
    (cwSquareBlockType 0 1 3) (cwRect013BasisOut K 6)
  refine ⟨maps, ?_, q6GradeThreeCoordinate.toEmbedding, ?_⟩
  · change PiTensorProduct.map maps
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 0 1 3)) = MMTensor K 1 1 12
    rw [cwSquareCanonical_blockTensor_eq_term_pairs]
    dsimp only [maps]
    simp only [map_sum, cwSquareBasisMap_term_pair]
    simpa only [cwRectTermTriple_eq_cwTermTriple] using
      cwRect013_all_filtered_term_pairs_eq_MMTensor K 6
  · intro p
    change maps 2 (q6GradeThreeZBasis K p) = _
    rw [q6GradeThreeZBasis_blockProj]
    dsimp only [maps]
    change cwSquareBasisMap K 6 1 1 12
        (cwSquareBlockType 0 1 3) (cwRect013BasisOut K 6) 2
          ((cwSquareCanonicalGrading K 6).blockProj 2
            (cwSquareBlockType 0 1 3 2)
            (cwSquareBasis K 6 2 p.down.1)) = _
    rw [cwSquareBasisMap_apply_blockProj_basis]
    have hgrade : cwPairGrade 6 p.down.1 = 3 := by
      simpa [cwPairGrade, cwSquarePairGrade, cwCoordGrade,
        cwSquareCoordGrade] using p.down.2
    rw [if_pos (show cwPairGrade 6 p.down.1 =
      cwSquareBlockType 0 1 3 2 by simpa using hgrade)]
    have hp := q6GradeThreeEquiv_source p.down
    generalize hc : q6GradeThreeEquiv p.down = c at hp
    rcases c with i | i
    · have hcoord : q6GradeThreeCoordinate.toEmbedding p =
          cwRectLeft 6 i := q6GradeThreeCoordinate_eq_left p i hc
      rw [hp, hcoord]
      simp [cwRect013BasisOut, cwRect013MMVec, cwM_eq_cwM_iff,
        cwT_ne_cwM]
    · have hcoord : q6GradeThreeCoordinate.toEmbedding p =
          cwRectRight 6 i := q6GradeThreeCoordinate_eq_right p i hc
      rw [hp, hcoord]
      simp [cwRect013BasisOut, cwRect013MMVec, cwM_eq_cwM_iff,
        cwT_ne_cwM]

private theorem q6GradeOne_left (i : Fin 6) :
    cwSquarePairGrade 6 (cwO 6, cwM 6 i) = 1 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, cwO, cwM, hiT]

private theorem q6GradeOne_right (i : Fin 6) :
    cwSquarePairGrade 6 (cwM 6 i, cwO 6) = 1 := by
  have hiT : i.val + 1 ≠ 7 := by omega
  simp [cwSquarePairGrade, cwSquareCoordGrade, cwO, cwM, hiT]

private def q6GradeOneEncode : Fin 6 ⊕ Fin 6 → CoarsePair 6 1
  | Sum.inl i => ⟨(cwO 6, cwM 6 i), q6GradeOne_left i⟩
  | Sum.inr i => ⟨(cwM 6 i, cwO 6), q6GradeOne_right i⟩

private def q6GradeOneDecode (p : CoarsePair 6 1) : Fin 6 ⊕ Fin 6 :=
  if p.1.1.val = 0 then
    Sum.inl (Fin.ofNat 6 (p.1.2.val - 1))
  else
    Sum.inr (Fin.ofNat 6 (p.1.1.val - 1))

private theorem q6GradeOneDecode_encode :
    Function.LeftInverse q6GradeOneDecode q6GradeOneEncode := by
  intro c
  rcases c with i | i <;> fin_cases i <;> rfl

private theorem q6GradeOneEncode_decode :
    Function.RightInverse q6GradeOneDecode q6GradeOneEncode := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [q6GradeOneDecode, q6GradeOneEncode, cwSquarePairGrade,
      cwSquareCoordGrade, cwM, cwO] at hp ⊢

private noncomputable def q6GradeOneEquiv :
    CoarsePair 6 1 ≃ (Fin 6 ⊕ Fin 6) where
  toFun := q6GradeOneDecode
  invFun := q6GradeOneEncode
  left_inv := q6GradeOneEncode_decode
  right_inv := q6GradeOneDecode_encode

private noncomputable def q6GradeOneCoordinate :
    LiftedCoarsePair.{u} 6 1 ≃ Fin 12 :=
  Equiv.ulift.trans <| q6GradeOneEquiv.trans (cwRectChannelEquiv 6)

private theorem q6GradeOneEquiv_source (p : CoarsePair 6 1) :
    p.1 =
      match q6GradeOneEquiv p with
      | Sum.inl i => (cwO 6, cwM 6 i)
      | Sum.inr i => (cwM 6 i, cwO 6) := by
  have h := q6GradeOneEquiv.symm_apply_apply p
  generalize hc : q6GradeOneEquiv p = c at h ⊢
  rcases c with i | i <;>
    simpa [q6GradeOneEquiv, q6GradeOneEncode] using
      congrArg Subtype.val h.symm

private theorem q6GradeOneCoordinate_eq_left
    (p : LiftedCoarsePair.{u} 6 1) (i : Fin 6)
    (h : q6GradeOneEquiv p.down = Sum.inl i) :
    q6GradeOneCoordinate p = cwRectLeft 6 i := by
  change cwRectChannelEquiv 6 (q6GradeOneEquiv p.down) = _
  rw [h]
  exact cwRectChannelEquiv_inl 6 i

private theorem q6GradeOneCoordinate_eq_right
    (p : LiftedCoarsePair.{u} 6 1) (i : Fin 6)
    (h : q6GradeOneEquiv p.down = Sum.inr i) :
    q6GradeOneCoordinate p = cwRectRight 6 i := by
  change cwRectChannelEquiv 6 (q6GradeOneEquiv p.down) = _
  rw [h]
  exact cwRectChannelEquiv_inr 6 i

private noncomputable def q6GradeOneZBasis
    (K : Type u) [Field K] :
    Basis (LiftedCoarsePair.{u} 6 1) K
      ((cwSquareCanonicalGrading K 6).classOf 2 1) :=
  (coarseClassBasis (K := K) 6 2 1).reindex Equiv.ulift.symm

private theorem q6GradeOneZBasis_blockProj
    (K : Type u) [Field K] (p : LiftedCoarsePair.{u} 6 1) :
    q6GradeOneZBasis K p =
      (cwSquareCanonicalGrading K 6).blockProj 2 1
        (cwSquareBasis K 6 2 p.down.1) := by
  apply Subtype.ext
  rw [TensorObj.TypeGrading.blockProj_apply_mem]
  · have hr :
        q6GradeOneZBasis K p =
          coarseClassBasis (K := K) 6 2 1 p.down := by
      exact Module.Basis.reindex_apply
        (coarseClassBasis (K := K) 6 2 1) Equiv.ulift.symm p
    rw [hr]
    exact mme_dwz_coarseClassBasis_q6_val K 2 1 p.down
  · exact Submodule.subset_span ⟨p.down.1, p.down.2, rfl⟩

/-- The canonical q=6 `031` restriction has an exact public grade-one
Z-basis router into the twelve standard channels of `⟨1,1,12⟩`. -/
theorem cwSquareCanonical_rect031_q6_Z_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 0 3 1 s) →ₗ[K]
          (MMObj K 1 1 12).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 0 3 1)) =
        MMTensor K 1 1 12 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single (coord p, (0 : Fin 1)) 1 : Fin 12 × Fin 1 → K) := by
  let maps := cwSquareBasisMap K 6 1 1 12
    (cwSquareBlockType 0 3 1) (cwRect031BasisOut K 6)
  refine ⟨maps, ?_, q6GradeOneCoordinate.toEmbedding, ?_⟩
  · change PiTensorProduct.map maps
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 0 3 1)) = MMTensor K 1 1 12
    rw [cwSquareCanonical_blockTensor_eq_term_pairs]
    dsimp only [maps]
    simp only [map_sum, cwSquareBasisMap_term_pair]
    simpa only [cwRectTermTriple_eq_cwTermTriple] using
      cwRect031_all_filtered_term_pairs_eq_MMTensor K 6
  · intro p
    change maps 2 (q6GradeOneZBasis K p) = _
    rw [q6GradeOneZBasis_blockProj]
    dsimp only [maps]
    change cwSquareBasisMap K 6 1 1 12
        (cwSquareBlockType 0 3 1) (cwRect031BasisOut K 6) 2
          ((cwSquareCanonicalGrading K 6).blockProj 2
            (cwSquareBlockType 0 3 1 2)
            (cwSquareBasis K 6 2 p.down.1)) = _
    rw [cwSquareBasisMap_apply_blockProj_basis]
    have hgrade : cwPairGrade 6 p.down.1 = 1 := by
      simpa [cwPairGrade, cwSquarePairGrade, cwCoordGrade,
        cwSquareCoordGrade] using p.down.2
    rw [if_pos (show cwPairGrade 6 p.down.1 =
      cwSquareBlockType 0 3 1 2 by simpa using hgrade)]
    have hp := q6GradeOneEquiv_source p.down
    generalize hc : q6GradeOneEquiv p.down = c at hp
    rcases c with i | i
    · have hcoord : q6GradeOneCoordinate.toEmbedding p =
          cwRectLeft 6 i := q6GradeOneCoordinate_eq_left p i hc
      rw [hp, hcoord]
      simp [cwRect031BasisOut, cwRect013MMVec, cwM_eq_cwM_iff,
        cwO_ne_cwM]
    · have hcoord : q6GradeOneCoordinate.toEmbedding p =
          cwRectRight 6 i := q6GradeOneCoordinate_eq_right p i hc
      rw [hp, hcoord]
      simp [cwRect031BasisOut, cwRect013MMVec, cwM_eq_cwM_iff,
        cwO_ne_cwM]

/-- The canonical q=6 `103` restriction has the rotated exact grade-three
Z-basis router into the twelve standard channels of `⟨12,1,1⟩`. -/
theorem cwSquareCanonical_rect103_q6_Z_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 1 0 3 s) →ₗ[K]
          (MMObj K 12 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 1 0 3)) =
        MMTensor K 12 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 3 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 3).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K) := by
  let maps := cwSquareBasisMap K 6 12 1 1
    (cwSquareBlockType 1 0 3) (cwRect103BasisOut K 6)
  refine ⟨maps, ?_, q6GradeThreeCoordinate.toEmbedding, ?_⟩
  · change PiTensorProduct.map maps
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 1 0 3)) = MMTensor K 12 1 1
    rw [cwSquareCanonical_blockTensor_eq_term_pairs]
    dsimp only [maps]
    simp only [map_sum, cwSquareBasisMap_term_pair]
    simpa only [cwRectTermTriple_eq_cwTermTriple] using
      cwRect103_all_filtered_term_pairs_eq_MMTensor K 6
  · intro p
    change maps 2 (q6GradeThreeZBasis K p) = _
    rw [q6GradeThreeZBasis_blockProj]
    dsimp only [maps]
    change cwSquareBasisMap K 6 12 1 1
        (cwSquareBlockType 1 0 3) (cwRect103BasisOut K 6) 2
          ((cwSquareCanonicalGrading K 6).blockProj 2
            (cwSquareBlockType 1 0 3 2)
            (cwSquareBasis K 6 2 p.down.1)) = _
    rw [cwSquareBasisMap_apply_blockProj_basis]
    have hgrade : cwPairGrade 6 p.down.1 = 3 := by
      simpa [cwPairGrade, cwSquarePairGrade, cwCoordGrade,
        cwSquareCoordGrade] using p.down.2
    rw [if_pos (show cwPairGrade 6 p.down.1 =
      cwSquareBlockType 1 0 3 2 by simpa using hgrade)]
    have hp := q6GradeThreeEquiv_source p.down
    generalize hc : q6GradeThreeEquiv p.down = c at hp
    rcases c with i | i
    · have hcoord : q6GradeThreeCoordinate.toEmbedding p =
          cwRectLeft 6 i := q6GradeThreeCoordinate_eq_left p i hc
      rw [hp, hcoord]
      simp [cwRect103BasisOut, cwRect103MMVec, cwM_eq_cwM_iff,
        cwT_ne_cwM]
    · have hcoord : q6GradeThreeCoordinate.toEmbedding p =
          cwRectRight 6 i := q6GradeThreeCoordinate_eq_right p i hc
      rw [hp, hcoord]
      simp [cwRect103BasisOut, cwRect103MMVec, cwM_eq_cwM_iff,
        cwT_ne_cwM]

/-- The canonical q=6 `301` restriction has the rotated exact grade-one
Z-basis router into the twelve standard channels of `⟨12,1,1⟩`. -/
theorem cwSquareCanonical_rect301_q6_Z_source_router
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 3 0 1 s) →ₗ[K]
          (MMObj K 12 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 3 0 1)) =
        MMTensor K 12 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K) := by
  let maps := cwSquareBasisMap K 6 12 1 1
    (cwSquareBlockType 3 0 1) (cwRect301BasisOut K 6)
  refine ⟨maps, ?_, q6GradeOneCoordinate.toEmbedding, ?_⟩
  · change PiTensorProduct.map maps
        ((cwSquareCanonicalGrading K 6).blockTensor
          (cwSquareBlockType 3 0 1)) = MMTensor K 12 1 1
    rw [cwSquareCanonical_blockTensor_eq_term_pairs]
    dsimp only [maps]
    simp only [map_sum, cwSquareBasisMap_term_pair]
    simpa only [cwRectTermTriple_eq_cwTermTriple] using
      cwRect301_all_filtered_term_pairs_eq_MMTensor K 6
  · intro p
    change maps 2 (q6GradeOneZBasis K p) = _
    rw [q6GradeOneZBasis_blockProj]
    dsimp only [maps]
    change cwSquareBasisMap K 6 12 1 1
        (cwSquareBlockType 3 0 1) (cwRect301BasisOut K 6) 2
          ((cwSquareCanonicalGrading K 6).blockProj 2
            (cwSquareBlockType 3 0 1 2)
            (cwSquareBasis K 6 2 p.down.1)) = _
    rw [cwSquareBasisMap_apply_blockProj_basis]
    have hgrade : cwPairGrade 6 p.down.1 = 1 := by
      simpa [cwPairGrade, cwSquarePairGrade, cwCoordGrade,
        cwSquareCoordGrade] using p.down.2
    rw [if_pos (show cwPairGrade 6 p.down.1 =
      cwSquareBlockType 3 0 1 2 by simpa using hgrade)]
    have hp := q6GradeOneEquiv_source p.down
    generalize hc : q6GradeOneEquiv p.down = c at hp
    rcases c with i | i
    · have hcoord : q6GradeOneCoordinate.toEmbedding p =
          cwRectLeft 6 i := q6GradeOneCoordinate_eq_left p i hc
      rw [hp, hcoord]
      simp [cwRect301BasisOut, cwRect103MMVec, cwM_eq_cwM_iff,
        cwO_ne_cwM]
    · have hcoord : q6GradeOneCoordinate.toEmbedding p =
          cwRectRight 6 i := q6GradeOneCoordinate_eq_right p i hc
      rw [hp, hcoord]
      simp [cwRect301BasisOut, cwRect103MMVec, cwM_eq_cwM_iff,
        cwO_ne_cwM]


end CWSquareCanonical

end MME

open MME
open MME.DWZComponentRestriction

universe u

theorem solution
    (K : Type u) [Field K] :
    ∃ maps : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K 6).classOf s
            (cwSquareBlockType 3 0 1 s) →ₗ[K]
          (MMObj K 12 1 1).V s,
      PiTensorProduct.map maps
          ((cwSquareCanonicalGrading K 6).blockTensor
            (cwSquareBlockType 3 0 1)) =
        MMTensor K 12 1 1 ∧
      ∃ coord : LiftedCoarsePair.{u} 6 1 ↪ Fin 12,
        ∀ p,
          maps 2
              (((coarseClassBasis (K := K) 6 2 1).reindex
                Equiv.ulift.symm) p) =
            (Pi.single ((0 : Fin 1), coord p) 1 : Fin 1 × Fin 12 → K) :=
  MME.cwSquareCanonical_rect301_q6_Z_source_router K
