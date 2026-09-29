-- Prove2me | solution 1 for mme_dwz_cw_square_central_022_202_source_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T03:57:21.395441+00:00
-- url     : https://prove2.me/submissions/3d7703a5-4247-44a6-b150-92c7ed1db9d6

import Definitions.Def_mme_dwz_cw_square_fine_central_channels
import Definitions.Def_mme_CW_square_canonical_grading
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

open PiTensorProduct TensorProduct BigOperators DirectSum Module

namespace MME.CanonicalCentralRouter

universe u

set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

section

variable {K : Type u} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V]
variable {ι κ : Type*} [DecidableEq κ]

private theorem router_basis_mem (b : Basis ι K V) (g : ι → κ) (i : ι) :
    b i ∈ cwBasisGrade b g (g i) := by
  exact Submodule.subset_span ⟨i, rfl, rfl⟩

end

private theorem cwSquareCanonical_blockProj_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (a : Fin 5) (i j : Fin (q + 2)) :
    (cwSquareCanonicalGrading K q).blockProj s a
        (cwSquareCanonicalBasis K q s (i, j)) =
      if h : cwSquarePairGrade q (i, j) = a then
        ⟨cwSquareCanonicalBasis K q s (i, j), by
          simpa [h] using
            router_basis_mem (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j)⟩
      else 0 := by
  split_ifs with h
  · subst a
    exact TensorObj.TypeGrading.blockProj_apply_mem
      (cwSquareCanonicalGrading K q) s (cwSquarePairGrade q (i, j)) _
      (router_basis_mem (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j))
  · exact TensorObj.TypeGrading.blockProj_apply_mem_ne
      (cwSquareCanonicalGrading K q) s a (cwSquarePairGrade q (i, j)) (Ne.symm h) _
      (router_basis_mem (cwSquareCanonicalBasis K q s) (cwSquarePairGrade q) (i, j))

private def cwVec
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) (a : Fin (q + 2)) :
    CWSpace K q s :=
  match s with
  | ⟨0, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨1, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)
  | ⟨2, _⟩ => (Pi.single a 1 : Fin (q + 2) → K)

private theorem cwSquareCanonicalBasis_apply
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

private theorem cwSquareCoordGrade_O (q : ℕ) : cwSquareCoordGrade q (cwO q) = 0 := by
  simp [cwSquareCoordGrade, cwO]

private theorem cwSquareCoordGrade_M (q : ℕ) (i : Fin q) :
    cwSquareCoordGrade q (cwM q i) = 1 := by
  simp [cwSquareCoordGrade, cwM]
  omega

private theorem cwSquareCoordGrade_T (q : ℕ) : cwSquareCoordGrade q (cwT q) = 2 := by
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
    simp [cwSquareCoordGrade_O, cwSquareCoordGrade_M, cwSquareCoordGrade_T]

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

private noncomputable def cwSquareCanonicalBasisMap
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s (σ s) →ₗ[K]
      (MMObj K n m p).V s :=
  ((cwSquareCanonicalBasis K q s).constr K (output s)).comp
    ((cwSquareCanonicalGrading K q).decomp s (σ s)).subtype

private theorem cwSquareCanonicalBasisMap_apply_blockProj_basis
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (s : Fin 3) (idx : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasisMap K q n m p σ output s
        ((cwSquareCanonicalGrading K q).blockProj s (σ s)
          (cwSquareCanonicalBasis K q s idx)) =
      if cwSquarePairGrade q idx = σ s then output s idx else 0 := by
  rw [cwSquareCanonical_blockProj_basis]
  split_ifs with hgrade
  · simp [cwSquareCanonicalBasisMap, Module.Basis.constr_basis]
  · simp [cwSquareCanonicalBasisMap]

private theorem cwSquareCanonicalBasisMap_term_pair
    (K : Type u) [Field K] (q n m p : ℕ)
    (σ : Fin 3 → Fin 5)
    (output : ∀ s : Fin 3,
      Fin (q + 2) × Fin (q + 2) → (MMObj K n m p).V s)
    (t u : CWTerm q) :
    PiTensorProduct.map (cwSquareCanonicalBasisMap K q n m p σ output)
        (PiTensorProduct.map
          (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
          (interchange (cwTermMonom K q t) (cwTermMonom K q u))) =
      tprod K (fun s =>
        if cwSquarePairGrade q
            (cwTermTriple q t s, cwTermTriple q u s) = σ s then
          output s (cwTermTriple q t s, cwTermTriple q u s)
        else 0) := by
  have hterm (v : CWTerm q) :
      cwTermMonom K q v =
        tprod K (fun s => cwVec K q s (cwTermTriple q v s)) := by
    unfold cwTermMonom CWMonom
    congr 1
    funext s
    fin_cases s <;> rfl
  rw [hterm t, hterm u]
  let v₁ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q t s)
  let v₂ : ∀ s, CWSpace K q s :=
    fun s => cwVec K q s (cwTermTriple q u s)
  change PiTensorProduct.map (cwSquareCanonicalBasisMap K q n m p σ output)
      (PiTensorProduct.map
        (fun s => (cwSquareCanonicalGrading K q).blockProj s (σ s))
        (interchange (tprod K v₁) (tprod K v₂))) = _
  have hinter := interchange_tprod (K := K) v₁ v₂
  refine (congrArg
    (fun z => PiTensorProduct.map (cwSquareCanonicalBasisMap K q n m p σ output)
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
    _ = PiTensorProduct.map (cwSquareCanonicalBasisMap K q n m p σ output)
        (tprod K (fun s =>
          (cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) := congrArg _ hinner
    _ = tprod K (fun s =>
        cwSquareCanonicalBasisMap K q n m p σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s)
            (v₁ s ⊗ₜ[K] v₂ s))) :=
      PiTensorProduct.map_tprod _ _
    _ = _ := by
      congr 1
      funext s
      dsimp [v₁, v₂]
      have hbasis := (cwSquareCanonicalBasis_apply K q s
        (cwTermTriple q t s) (cwTermTriple q u s)).symm
      refine (congrArg
        (fun z => cwSquareCanonicalBasisMap K q n m p σ output s
          ((cwSquareCanonicalGrading K q).blockProj s (σ s) z)) hbasis).trans ?_
      exact cwSquareCanonicalBasisMap_apply_blockProj_basis
        K q n m p σ output s _

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
    simp [cwRectTermTriple, cwSquarePairGrade, cwSquareCoordGrade_O,
      cwSquareCoordGrade_M, cwSquareCoordGrade_T]

private theorem cwCentral022ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 0 2 2 s) :
    cwCentral022ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCentral022ExpectedTermPair, cwSquarePairGrade,
      cwSquareCoordGrade_O, cwSquareCoordGrade_M, cwSquareCoordGrade_T,
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
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral022ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral022BasisOut, cwCentral022MMVec,
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral022ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral022BasisOut, cwCentral022MMVec,
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_M,
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
  let maps := cwSquareCanonicalBasisMap K q 1 1 (q ^ 2 + 2)
    (cwSquareBlockType 0 2 2) (cwCentral022BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 2 2)) = MMTensor K 1 1 (q ^ 2 + 2)
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareCanonicalBasisMap_term_pair]
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
    simp [cwRectTermTriple, cwSquarePairGrade, cwSquareCoordGrade_O,
      cwSquareCoordGrade_M, cwSquareCoordGrade_T]

private theorem cwCentral202ExpectedTermPair_eq_zero_of_grade_mismatch
    (K : Type u) [Field K] (q : ℕ) (t u : CWTerm q) (s : Fin 3)
    (hgrade : cwSquarePairGrade q
      (cwRectTermTriple q t s, cwRectTermTriple q u s) ≠
        cwSquareBlockType 2 0 2 s) :
    cwCentral202ExpectedTermPair K q t u = 0 := by
  rcases t with ⟨i, a⟩ | a <;> rcases u with ⟨j, b⟩ | b <;>
    fin_cases a <;> fin_cases b <;> fin_cases s <;>
    simp [cwRectTermTriple, cwCentral202ExpectedTermPair, cwSquarePairGrade,
      cwSquareCoordGrade_O, cwSquareCoordGrade_M, cwSquareCoordGrade_T,
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
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral202ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral202BasisOut, cwCentral202MMVec,
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_T,
        cwSquareBlockType, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · simp only [cwCentral202ExpectedTermPair]
    congr 1
    funext s
    fin_cases s <;>
      simp [cwRectTermTriple, cwCentral202BasisOut, cwCentral202MMVec,
        cwSquarePairGrade, cwSquareCoordGrade_O, cwSquareCoordGrade_M,
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
  let maps := cwSquareCanonicalBasisMap K q (q ^ 2 + 2) 1 1
    (cwSquareBlockType 2 0 2) (cwCentral202BasisOut K q)
  refine ⟨maps, ?_⟩
  change PiTensorProduct.map maps
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 2 0 2)) = MMTensor K (q ^ 2 + 2) 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  dsimp only [maps]
  simp only [map_sum, cwSquareCanonicalBasisMap_term_pair]
  simpa only [cwRectTermTriple_eq_cwTermTriple] using
    cwCentral202_all_filtered_term_pairs_eq_MMTensor K q



/-! ## Public source-faithful central router interface -/

noncomputable def centralIndexEquiv (q : ℕ) :
    (Fin 2 ⊕ (Fin q × Fin q)) ≃ Fin (q ^ 2 + 2) :=
  cwCentralIndexEquiv q

noncomputable def central022MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K 1 1 (q ^ 2 + 2)).V s :=
  cwCentral022MMVec K q k

noncomputable def central202MMVec
    (K : Type u) [Field K] (q : ℕ) (k : Fin (q ^ 2 + 2)) :
    ∀ s : Fin 3, (MMObj K (q ^ 2 + 2) 1 1).V s :=
  cwCentral202MMVec K q k

noncomputable def central022BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K 1 1 (q ^ 2 + 2)).V s :=
  cwCentral022BasisOut K q s ab

noncomputable def central202BasisOut
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    (MMObj K (q ^ 2 + 2) 1 1).V s :=
  cwCentral202BasisOut K q s ab

/-- The exact canonical CW-square basis pair naming each 022 channel.  Its
domain is the router's native order: two special channels followed by the
`q^2` middle channels. -/
def central022SourcePair (q : ℕ) (c : Fin 2 ⊕ (Fin q × Fin q)) :
    Fin 3 → Fin (q + 2) × Fin (q + 2)
  | ⟨0, _⟩ => (cwO q, cwO q)
  | ⟨1, _⟩ =>
      match c with
      | Sum.inl k => if k = 0 then (cwO q, cwT q) else (cwT q, cwO q)
      | Sum.inr ij => (cwM q ij.1, cwM q ij.2)
  | ⟨2, _⟩ =>
      match c with
      | Sum.inl k => if k = 0 then (cwT q, cwO q) else (cwO q, cwT q)
      | Sum.inr ij => (cwM q ij.1, cwM q ij.2)

/-- The 202 rotation of `central022SourcePair`, using the same channel
coordinate. -/
def central202SourcePair (q : ℕ) (c : Fin 2 ⊕ (Fin q × Fin q)) :
    Fin 3 → Fin (q + 2) × Fin (q + 2)
  | ⟨0, _⟩ =>
      match c with
      | Sum.inl k => if k = 0 then (cwO q, cwT q) else (cwT q, cwO q)
      | Sum.inr ij => (cwM q ij.1, cwM q ij.2)
  | ⟨1, _⟩ => (cwO q, cwO q)
  | ⟨2, _⟩ =>
      match c with
      | Sum.inl k => if k = 0 then (cwT q, cwO q) else (cwO q, cwT q)
      | Sum.inr ij => (cwM q ij.1, cwM q ij.2)

theorem central022BasisOut_source
    (K : Type u) [Field K] (q : ℕ)
    (c : Fin 2 ⊕ (Fin q × Fin q)) (s : Fin 3) :
    central022BasisOut K q s (central022SourcePair q c s) =
      central022MMVec K q (centralIndexEquiv q c) s := by
  rcases c with k | ij
  · fin_cases k <;> fin_cases s <;>
      simp [central022BasisOut, central022MMVec, centralIndexEquiv,
        central022SourcePair, cwCentral022BasisOut, cwCentral022MMVec,
        cwCentralIndexEquiv, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · rcases ij with ⟨i, j⟩
    fin_cases s <;>
      simp [central022BasisOut, central022MMVec, centralIndexEquiv,
        central022SourcePair, cwCentral022BasisOut, cwCentral022MMVec,
        cwCentralIndexEquiv, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]

theorem central202BasisOut_source
    (K : Type u) [Field K] (q : ℕ)
    (c : Fin 2 ⊕ (Fin q × Fin q)) (s : Fin 3) :
    central202BasisOut K q s (central202SourcePair q c s) =
      central202MMVec K q (centralIndexEquiv q c) s := by
  rcases c with k | ij
  · fin_cases k <;> fin_cases s <;>
      simp [central202BasisOut, central202MMVec, centralIndexEquiv,
        central202SourcePair, cwCentral202BasisOut, cwCentral202MMVec,
        cwCentralIndexEquiv, cwO_ne_cwM, cwT_ne_cwM, cwO_ne_cwT]
  · rcases ij with ⟨i, j⟩
    fin_cases s <;>
      simp [central202BasisOut, central202MMVec, centralIndexEquiv,
        central202SourcePair, cwCentral202BasisOut, cwCentral202MMVec,
        cwCentralIndexEquiv, cwM_eq_cwM_iff, cwO_ne_cwM, cwT_ne_cwM,
        cwM_ne_cwO, cwM_ne_cwT, cwO_ne_cwT, eq_comm]

noncomputable def central022Maps
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s
        (cwSquareBlockType 0 2 2 s) →ₗ[K]
      (MMObj K 1 1 (q ^ 2 + 2)).V s :=
  cwSquareCanonicalBasisMap K q 1 1 (q ^ 2 + 2)
    (cwSquareBlockType 0 2 2) (cwCentral022BasisOut K q) s

noncomputable def central202Maps
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3) :
    (cwSquareCanonicalGrading K q).classOf s
        (cwSquareBlockType 2 0 2 s) →ₗ[K]
      (MMObj K (q ^ 2 + 2) 1 1).V s :=
  cwSquareCanonicalBasisMap K q (q ^ 2 + 2) 1 1
    (cwSquareBlockType 2 0 2) (cwCentral202BasisOut K q) s

theorem central022Maps_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    central022Maps K q s
        ((cwSquareCanonicalGrading K q).blockProj s
          (cwSquareBlockType 0 2 2 s)
          (cwSquareCanonicalBasis K q s ab)) =
      if cwSquarePairGrade q ab = cwSquareBlockType 0 2 2 s then
        central022BasisOut K q s ab
      else 0 := by
  exact cwSquareCanonicalBasisMap_apply_blockProj_basis
    K q 1 1 (q ^ 2 + 2) (cwSquareBlockType 0 2 2)
      (cwCentral022BasisOut K q) s ab

theorem central202Maps_basis
    (K : Type u) [Field K] (q : ℕ) (s : Fin 3)
    (ab : Fin (q + 2) × Fin (q + 2)) :
    central202Maps K q s
        ((cwSquareCanonicalGrading K q).blockProj s
          (cwSquareBlockType 2 0 2 s)
          (cwSquareCanonicalBasis K q s ab)) =
      if cwSquarePairGrade q ab = cwSquareBlockType 2 0 2 s then
        central202BasisOut K q s ab
      else 0 := by
  exact cwSquareCanonicalBasisMap_apply_blockProj_basis
    K q (q ^ 2 + 2) 1 1 (cwSquareBlockType 2 0 2)
      (cwCentral202BasisOut K q) s ab

theorem central022Maps_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (central022Maps K q)
        ((cwSquareCanonicalGrading K q).blockTensor
          (cwSquareBlockType 0 2 2)) =
      MMTensor K 1 1 (q ^ 2 + 2) := by
  change PiTensorProduct.map
      (cwSquareCanonicalBasisMap K q 1 1 (q ^ 2 + 2)
        (cwSquareBlockType 0 2 2) (cwCentral022BasisOut K q))
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 0 2 2)) = MMTensor K 1 1 (q ^ 2 + 2)
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  simp only [map_sum, cwSquareCanonicalBasisMap_term_pair]
  simpa only [central022BasisOut,
      cwRectTermTriple_eq_cwTermTriple] using
    cwCentral022_all_filtered_term_pairs_eq_MMTensor K q

theorem central202Maps_tensor
    (K : Type u) [Field K] (q : ℕ) :
    PiTensorProduct.map (central202Maps K q)
        ((cwSquareCanonicalGrading K q).blockTensor
          (cwSquareBlockType 2 0 2)) =
      MMTensor K (q ^ 2 + 2) 1 1 := by
  change PiTensorProduct.map
      (cwSquareCanonicalBasisMap K q (q ^ 2 + 2) 1 1
        (cwSquareBlockType 2 0 2) (cwCentral202BasisOut K q))
      ((cwSquareCanonicalGrading K q).blockTensor
        (cwSquareBlockType 2 0 2)) = MMTensor K (q ^ 2 + 2) 1 1
  rw [cwSquareCanonical_blockTensor_eq_term_pairs]
  simp only [map_sum, cwSquareCanonicalBasisMap_term_pair]
  simpa only [central202BasisOut,
      cwRectTermTriple_eq_cwTermTriple] using
    cwCentral202_all_filtered_term_pairs_eq_MMTensor K q

end MME.CanonicalCentralRouter

open PiTensorProduct
open MME
open MME.DWZFineChannel

universe u

set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem solution
    (K : Type u) [Field K] (q : ℕ) :
    (∃ maps022 : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K q).classOf s
            (cwSquareBlockType 0 2 2 s) →ₗ[K]
          (MMObj K 1 1 (q ^ 2 + 2)).V s,
      PiTensorProduct.map maps022
          ((cwSquareCanonicalGrading K q).blockTensor
            (cwSquareBlockType 0 2 2)) =
        MMTensor K 1 1 (q ^ 2 + 2) ∧
      ∀ (c : Fine022Channel q) (s : Fin 3),
        maps022 s
            ((cwSquareCanonicalGrading K q).blockProj s
              (cwSquareBlockType 0 2 2 s)
              (cwSquareCanonicalBasis K q s (fine022SourcePair q c s))) =
          fine022MMVec K q (fine022ChannelEquiv q c) s) ∧
    (∃ maps202 : ∀ s : Fin 3,
        (cwSquareCanonicalGrading K q).classOf s
            (cwSquareBlockType 2 0 2 s) →ₗ[K]
          (MMObj K (q ^ 2 + 2) 1 1).V s,
      PiTensorProduct.map maps202
          ((cwSquareCanonicalGrading K q).blockTensor
            (cwSquareBlockType 2 0 2)) =
        MMTensor K (q ^ 2 + 2) 1 1 ∧
      ∀ (c : Fine202Channel q) (s : Fin 3),
        maps202 s
            ((cwSquareCanonicalGrading K q).blockProj s
              (cwSquareBlockType 2 0 2 s)
              (cwSquareCanonicalBasis K q s (fine202SourcePair q c s))) =
          fine202MMVec K q (fine202ChannelEquiv q c) s) := by
  have hO : cwSquareCoordGrade q (cwO q) = 0 := by
    simp [cwSquareCoordGrade, cwO]
  have hM : ∀ i : Fin q, cwSquareCoordGrade q (cwM q i) = 1 := by
    intro i
    simp [cwSquareCoordGrade, cwM]
    omega
  have hT : cwSquareCoordGrade q (cwT q) = 2 := by
    simp [cwSquareCoordGrade, cwT]
  constructor
  · refine ⟨MME.CanonicalCentralRouter.central022Maps K q,
      MME.CanonicalCentralRouter.central022Maps_tensor K q, ?_⟩
    intro c s
    have hgrade :
        cwSquarePairGrade q (fine022SourcePair q c s) =
          cwSquareBlockType 0 2 2 s := by
      rcases c with c | c
      · fin_cases c
        fin_cases s <;> simp [fine022SourcePair, cwSquarePairGrade,
          cwSquareBlockType, hO, hT]
      · rcases c with ij | c
        · rcases ij with ⟨i, j⟩
          fin_cases s <;> simp [fine022SourcePair, cwSquarePairGrade,
            cwSquareBlockType, hO, hM]
        · fin_cases c
          fin_cases s <;> simp [fine022SourcePair, cwSquarePairGrade,
            cwSquareBlockType, hO, hT]
    rw [MME.CanonicalCentralRouter.central022Maps_basis, if_pos hgrade]
    have hpair :
        fine022SourcePair q c s =
          MME.CanonicalCentralRouter.central022SourcePair q
            (fine022ToCentralSum q c) s := by
      rcases c with c | c
      · fin_cases c
        fin_cases s <;> rfl
      · rcases c with ij | c
        · fin_cases s <;> rfl
        · fin_cases c
          fin_cases s <;> rfl
    rw [hpair,
      MME.CanonicalCentralRouter.central022BasisOut_source K q
        (fine022ToCentralSum q c) s]
    rfl

  · refine ⟨MME.CanonicalCentralRouter.central202Maps K q,
      MME.CanonicalCentralRouter.central202Maps_tensor K q, ?_⟩
    intro c s
    have hgrade :
        cwSquarePairGrade q (fine202SourcePair q c s) =
          cwSquareBlockType 2 0 2 s := by
      rcases c with c | c
      · fin_cases c
        fin_cases s <;> simp [fine202SourcePair, cwSquarePairGrade,
          cwSquareBlockType, hO, hT]
      · rcases c with ij | c
        · rcases ij with ⟨i, j⟩
          fin_cases s <;> simp [fine202SourcePair, cwSquarePairGrade,
            cwSquareBlockType, hO, hM]
        · fin_cases c
          fin_cases s <;> simp [fine202SourcePair, cwSquarePairGrade,
            cwSquareBlockType, hO, hT]
    rw [MME.CanonicalCentralRouter.central202Maps_basis, if_pos hgrade]
    have hpair :
        fine202SourcePair q c s =
          MME.CanonicalCentralRouter.central202SourcePair q
            (fine022ToCentralSum q c) s := by
      rcases c with c | c
      · fin_cases c
        fin_cases s <;> rfl
      · rcases c with ij | c
        · fin_cases s <;> rfl
        · fin_cases c
          fin_cases s <;> rfl
    rw [hpair,
      MME.CanonicalCentralRouter.central202BasisOut_source K q
        (fine022ToCentralSum q c) s]
    rfl
