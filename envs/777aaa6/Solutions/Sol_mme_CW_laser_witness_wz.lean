-- Prove2me | solution 1 for mme_CW_laser_witness_wz
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-01T15:45:35.39238+00:00
-- url     : https://prove2.me/submissions/d9a1f557-2f77-496b-a45b-f87de56778e8

import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_tensor_type_grading
import Definitions.Def_mme_laser_pattern
import Definitions.Def_mme_laser_value_formula_wz
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # `Sol_mme_CW_laser_witness_wz` — self-contained sorry-free proof.

Constructs the canonical CW 3-grading on `CWObj K 6` and the canonical
support pattern. Then exhibits the uniform-1/6 distribution on the 6-element
`CWSupportPattern` to certify `5/2 ≤ laserValueFormula_wz G S`.

Self-contained: depends only on uploaded `Definitions/` and Mathlib (does NOT
depend on the auxiliary namespace from `Thm_mme_CW_canonical_aligned_witness`
which is local-only).

Mathematical content:
* Canonical 3-grading on `Fin 8 → K`: class 0 spans `{e_0}` (dim 1),
  class 1 spans `{e_1, …, e_6}` (dim 6), class 2 spans `{e_7}` (dim 1).
* For σ ∈ CWSupportPattern, dim-product is 36 (middle types) or 1 (boundary).
* Uniform π σ = 1/6 gives entropy log₂ 6, dim-term (1/3) log₂ 6,
  total exponent (4/3) log₂ 6.
* V = 6^(4/3) ≥ 5/2 since (5/2)^3 = 125/8 ≤ 1296 = 6^4. -/

open MME

universe u

namespace MMECWLaserWitnessWZSol

variable {K : Type u} [Field K]

/-! ## Local canonical grading machinery (self-contained)

A local copy of the typeOf/gradePiece construction, parameterised by q. -/

/-- The "type" of an index `k : Fin (q+2)`: `0` for the left boundary `0`,
`2` for the right boundary `q+1`, `1` for anything in between. -/
def typeOf (q : ℕ) (k : Fin (q+2)) : Fin 3 :=
  if k.val = 0 then 0
  else if k.val = q + 1 then 2
  else 1

/-- The `α`-th piece of the canonical 3-grading on `Fin (q+2) → K`. -/
def gradePiece (K : Type u) [Field K] (q : ℕ) (α : Fin 3) :
    Submodule K (Fin (q+2) → K) :=
  Submodule.span K (Set.range (fun k : {k : Fin (q+2) // typeOf q k = α} =>
    (Pi.single (k : Fin (q+2)) (1 : K) : Fin (q+2) → K)))

/-- Membership characterization: `f ∈ gradePiece K q α` iff `f` vanishes off the
`α`-th type-class. -/
lemma mem_gradePiece_iff (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    f ∈ gradePiece K q α ↔ ∀ k : Fin (q+2), typeOf q k ≠ α → f k = 0 := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction (p := fun g _ => ∀ k, typeOf q k ≠ α → g k = 0)
      ?_ ?_ ?_ ?_ hf
    · rintro g ⟨k, rfl⟩ j hj
      by_cases hjk : j = (k : Fin (q+2))
      · subst hjk; exact absurd k.2 hj
      · simp [Pi.single_apply, if_neg hjk]
    · intro k _; rfl
    · intro x y _ _ hx hy k hk
      simp [hx k hk, hy k hk]
    · intro c x _ hx k hk
      simp [hx k hk]
  · intro h
    have hsum :
        f = ∑ k ∈ (Finset.univ.filter (fun k : Fin (q+2) => typeOf q k = α)),
                f k • (Pi.single k (1 : K) : Fin (q+2) → K) := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      by_cases hj : typeOf q j = α
      · rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hk
          have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
            simp [Pi.single_apply, if_neg (Ne.symm hk)]
          rw [this]; ring
        · intro hjmem
          exfalso; apply hjmem
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      · symm
        rw [h j hj]
        apply Finset.sum_eq_zero
        intro k hk
        rw [Finset.mem_filter] at hk
        have hkj : j ≠ k := by
          intro heq
          rw [heq] at hj
          exact hj hk.2
        have : (Pi.single k (1 : K) : Fin (q+2) → K) j = 0 := by
          simp [Pi.single_apply, if_neg hkj]
        rw [this]; ring
    rw [hsum]
    apply Submodule.sum_mem
    intro k hk
    rw [Finset.mem_filter] at hk
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨⟨k, hk.2⟩, rfl⟩

lemma single_mem_gradePiece (q : ℕ) (k : Fin (q+2)) :
    (Pi.single k 1 : Fin (q+2) → K) ∈ gradePiece K q (typeOf q k) := by
  apply Submodule.subset_span
  exact ⟨⟨k, rfl⟩, rfl⟩

/-- Projection helper. -/
def project (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) : Fin (q+2) → K :=
  fun k => if typeOf q k = α then f k else 0

lemma project_mem (q : ℕ) (α : Fin 3) (f : Fin (q+2) → K) :
    project q α f ∈ gradePiece K q α := by
  rw [mem_gradePiece_iff]
  intro k hk
  simp [project, hk]

lemma sum_project (q : ℕ) (f : Fin (q+2) → K) :
    (∑ α : Fin 3, project q α f) = f := by
  funext k
  simp only [Finset.sum_apply, project]
  have : ∑ α : Fin 3, (if typeOf q k = α then f k else 0) = f k := by
    rw [Finset.sum_eq_single (typeOf q k)]
    · simp
    · intros α _ hα
      rw [if_neg (Ne.symm hα)]
    · intro h; exact absurd (Finset.mem_univ _) h
  exact this

/-- Internal-direct-sum property: each mode-space decomposes as a direct sum. -/
lemma isInternal_gradePiece (q : ℕ) :
    DirectSum.IsInternal (fun α : Fin 3 => gradePiece K q α) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨?_, ?_⟩
  · rw [iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero]
    intro s v hv hsum α hα
    have hvα : ∀ k, typeOf q k ≠ α → v α k = 0 :=
      (mem_gradePiece_iff q α (v α)).mp (hv α hα)
    funext k
    have hk_sum : (∑ β ∈ s, v β) k = 0 := by rw [hsum]; rfl
    rw [Finset.sum_apply] at hk_sum
    by_cases hk : typeOf q k = α
    · have hall : ∀ β ∈ s, β ≠ α → v β k = 0 := by
        intro β hβ hβne
        have hvβ : ∀ j, typeOf q j ≠ β → v β j = 0 :=
          (mem_gradePiece_iff q β (v β)).mp (hv β hβ)
        apply hvβ
        rw [hk]; exact hβne.symm
      rw [← Finset.add_sum_erase s _ hα] at hk_sum
      have hzero : (∑ β ∈ s.erase α, v β k) = 0 := by
        apply Finset.sum_eq_zero
        intro β hβ
        rw [Finset.mem_erase] at hβ
        exact hall β hβ.2 hβ.1
      rw [hzero, add_zero] at hk_sum
      exact hk_sum
    · exact hvα k hk
  · rw [eq_top_iff]
    intro f _
    rw [← sum_project q f]
    apply Submodule.sum_mem
    intro α _
    exact Submodule.mem_iSup_of_mem α (project_mem q α f)

/-- The canonical 3-grading on `CWObj K q`. -/
noncomputable def canonicalGrading (q : ℕ) : (CWObj K q).TypeGrading 3 where
  decomp := fun i α =>
    match i with
    | ⟨0, _⟩ => gradePiece K q α
    | ⟨1, _⟩ => gradePiece K q α
    | ⟨2, _⟩ => gradePiece K q α
  is_internal := fun i => by
    match i with
    | ⟨0, _⟩ => exact isInternal_gradePiece q
    | ⟨1, _⟩ => exact isInternal_gradePiece q
    | ⟨2, _⟩ => exact isInternal_gradePiece q

@[simp] lemma typeOf_zero (q : ℕ) :
    typeOf q (⟨0, by omega⟩ : Fin (q+2)) = 0 := by
  simp [typeOf]

@[simp] lemma typeOf_qPlusOne (q : ℕ) :
    typeOf q (⟨q+1, by omega⟩ : Fin (q+2)) = 2 := by
  simp [typeOf]

@[simp] lemma typeOf_middle (q : ℕ) (i : Fin q) :
    typeOf q (⟨i.val + 1, by omega⟩ : Fin (q+2)) = 1 := by
  simp [typeOf]
  intro h
  omega

/-! ## Witness construction for LaserAlignedSupport (local copy) -/

/-- Factor function for a triple of indices `(a, b, c)`. -/
def factorFun (q : ℕ) (a b c : Fin (q+2)) :
    ∀ i : Fin 3, CWSpace K q i :=
  fun i =>
    match i with
    | ⟨0, _⟩ => (Pi.single a (1 : K) : Fin (q+2) → K)
    | ⟨1, _⟩ => (Pi.single b (1 : K) : Fin (q+2) → K)
    | ⟨2, _⟩ => (Pi.single c (1 : K) : Fin (q+2) → K)

/-- Factor function for the rank-one term. -/
def fSum (K : Type u) [Field K] (q : ℕ) :
    (Fin q × Fin 3) ⊕ Fin 3 → ∀ i : Fin 3, CWSpace K q i :=
  fun s =>
    let O : Fin (q+2) := ⟨0, by omega⟩
    let T : Fin (q+2) := ⟨q+1, by omega⟩
    match s with
    | Sum.inl (i, r) =>
      let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
      match r with
      | ⟨0, _⟩ => factorFun (K := K) q O M M
      | ⟨1, _⟩ => factorFun (K := K) q M O M
      | ⟨2, _⟩ => factorFun (K := K) q M M O
    | Sum.inr r =>
      match r with
      | ⟨0, _⟩ => factorFun (K := K) q O O T
      | ⟨1, _⟩ => factorFun (K := K) q O T O
      | ⟨2, _⟩ => factorFun (K := K) q T O O

/-- Type-triple of each indexed rank-one term. -/
def τSum (q : ℕ) : (Fin q × Fin 3) ⊕ Fin 3 → Fin 3 × Fin 3 × Fin 3 :=
  fun s => match s with
    | Sum.inl (_, r) =>
      match r with
      | ⟨0, _⟩ => (0, 1, 1)
      | ⟨1, _⟩ => (1, 0, 1)
      | ⟨2, _⟩ => (1, 1, 0)
    | Sum.inr r =>
      match r with
      | ⟨0, _⟩ => (0, 0, 2)
      | ⟨1, _⟩ => (0, 2, 0)
      | ⟨2, _⟩ => (2, 0, 0)

lemma tprod_fSum (q : ℕ) (s : (Fin q × Fin 3) ⊕ Fin 3) :
    PiTensorProduct.tprod K (fSum K q s) =
      (match s with
       | Sum.inl (i, r) =>
         let O : Fin (q+2) := ⟨0, by omega⟩
         let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
         match r with
         | ⟨0, _⟩ => CWMonom K q O M M
         | ⟨1, _⟩ => CWMonom K q M O M
         | ⟨2, _⟩ => CWMonom K q M M O
       | Sum.inr r =>
         let O : Fin (q+2) := ⟨0, by omega⟩
         let T : Fin (q+2) := ⟨q+1, by omega⟩
         match r with
         | ⟨0, _⟩ => CWMonom K q O O T
         | ⟨1, _⟩ => CWMonom K q O T O
         | ⟨2, _⟩ => CWMonom K q T O O) := by
  rcases s with ⟨i, r⟩ | r
  · match r with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl
  · match r with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨2, _⟩ => rfl

lemma sum_tprod_fSum_eq (q : ℕ) :
    (∑ s : (Fin q × Fin 3) ⊕ Fin 3, PiTensorProduct.tprod K (fSum K q s)) =
      CWTensor K q := by
  rw [Fintype.sum_sum_type]
  have hL : (∑ p : Fin q × Fin 3, PiTensorProduct.tprod K (fSum K q (Sum.inl p))) =
      ∑ i : Fin q,
        let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
        let O : Fin (q+2) := ⟨0, by omega⟩
        CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    show PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 0))) +
         (PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 1))) +
          PiTensorProduct.tprod K (fSum K q (Sum.inl (i, 2)))) =
      let M : Fin (q+2) := ⟨i.val + 1, by omega⟩
      let O : Fin (q+2) := ⟨0, by omega⟩
      CWMonom K q O M M + CWMonom K q M O M + CWMonom K q M M O
    simp only [tprod_fSum]
    show CWMonom K q _ _ _ + (CWMonom K q _ _ _ + CWMonom K q _ _ _)
       = CWMonom K q _ _ _ + CWMonom K q _ _ _ + CWMonom K q _ _ _
    abel
  have hR : (∑ r : Fin 3, PiTensorProduct.tprod K (fSum K q (Sum.inr r))) =
      let O : Fin (q+2) := ⟨0, by omega⟩
      let T : Fin (q+2) := ⟨q+1, by omega⟩
      CWMonom K q O O T + CWMonom K q O T O + CWMonom K q T O O := by
    rw [show (Finset.univ : Finset (Fin 3)) = {0, 1, 2} by decide]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_singleton]
    simp only [tprod_fSum]
    show CWMonom K q _ _ _ + (CWMonom K q _ _ _ + CWMonom K q _ _ _) =
         CWMonom K q _ _ _ + CWMonom K q _ _ _ + CWMonom K q _ _ _
    abel
  rw [hL, hR]
  unfold CWTensor
  simp only [add_assoc]

/-! ## LaserAlignedSupport for the canonical grading -/

theorem canonicalGrading_aligned (q : ℕ) :
    TensorObj.LaserAlignedSupport
      (canonicalGrading q : (CWObj K q).TypeGrading 3)
      CWSupportPattern := by
  classical
  let σ : (Fin q × Fin 3) ⊕ Fin 3 ≃ Fin (q * 3 + 3) :=
    (Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv
  let k := q * 3 + 3
  let f : Fin k → ∀ i : Fin 3, (CWObj K q).V i :=
    fun j => fSum K q (σ.symm j)
  let τ : Fin k → Fin 3 × Fin 3 × Fin 3 :=
    fun j => τSum q (σ.symm j)
  refine ⟨k, f, τ, ?_, ?_⟩
  · show CWTensor K q = ∑ j, PiTensorProduct.tprod K (f j)
    rw [← sum_tprod_fSum_eq (K := K) q]
    exact (Fintype.sum_equiv σ.symm _ _ (fun _ => rfl)).symm
  · intro j
    have hO : ∀ (α : Fin 3),
        typeOf q (⟨0, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨0, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          gradePiece K q α := by
      intro α hα
      have := single_mem_gradePiece (K := K) q (⟨0, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    have hT : ∀ (α : Fin 3),
        typeOf q (⟨q+1, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨q+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          gradePiece K q α := by
      intro α hα
      have := single_mem_gradePiece (K := K) q (⟨q+1, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    have hM : ∀ (i : Fin q) (α : Fin 3),
        typeOf q (⟨i.val+1, by omega⟩ : Fin (q+2)) = α →
        (Pi.single (⟨i.val+1, by omega⟩ : Fin (q+2)) (1 : K) : Fin (q+2) → K) ∈
          gradePiece K q α := by
      intro i α hα
      have := single_mem_gradePiece (K := K) q (⟨i.val+1, by omega⟩ : Fin (q+2))
      rw [hα] at this; exact this
    show τSum q (σ.symm j) ∈ CWSupportPattern ∧ _
    revert j
    suffices ∀ s : (Fin q × Fin 3) ⊕ Fin 3,
        τSum q s ∈ CWSupportPattern ∧
        fSum K q s 0 ∈
          (canonicalGrading (K := K) q).classOf 0 (τSum q s).1 ∧
        fSum K q s 1 ∈
          (canonicalGrading (K := K) q).classOf 1 (τSum q s).2.1 ∧
        fSum K q s 2 ∈
          (canonicalGrading (K := K) q).classOf 2 (τSum q s).2.2 by
      intro j
      exact this (σ.symm j)
    intro s
    rcases s with ⟨i, r⟩ | r
    · match r with
      | ⟨0, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 1, 1) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (typeOf_zero q)
        · exact hM i 1 (typeOf_middle q i)
        · exact hM i 1 (typeOf_middle q i)
      | ⟨1, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((1, 0, 1) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hM i 1 (typeOf_middle q i)
        · exact hO 0 (typeOf_zero q)
        · exact hM i 1 (typeOf_middle q i)
      | ⟨2, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((1, 1, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hM i 1 (typeOf_middle q i)
        · exact hM i 1 (typeOf_middle q i)
        · exact hO 0 (typeOf_zero q)
    · match r with
      | ⟨0, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 0, 2) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (typeOf_zero q)
        · exact hO 0 (typeOf_zero q)
        · exact hT 2 (typeOf_qPlusOne q)
      | ⟨1, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((0, 2, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hO 0 (typeOf_zero q)
        · exact hT 2 (typeOf_qPlusOne q)
        · exact hO 0 (typeOf_zero q)
      | ⟨2, _⟩ =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · show ((2, 0, 0) : Fin 3 × Fin 3 × Fin 3) ∈ CWSupportPattern; decide
        · exact hT 2 (typeOf_qPlusOne q)
        · exact hO 0 (typeOf_zero q)
        · exact hO 0 (typeOf_zero q)

/-! ## Dimension computations at q=6 -/

/-- Indicator family used in gradePiece. -/
private noncomputable def indFamily (q : ℕ) (α : Fin 3) :
    {k : Fin (q+2) // typeOf q k = α} → (Fin (q+2) → K) :=
  fun k => (Pi.single (k : Fin (q+2)) (1 : K) : Fin (q+2) → K)

private lemma indFamily_linearIndependent (q : ℕ) (α : Fin 3) :
    LinearIndependent K (indFamily (K := K) q α) := by
  have hbasis : LinearIndependent K (fun i : Fin (q+2) =>
      (Pi.single i (1 : K) : Fin (q+2) → K)) := by
    have heq : (fun i : Fin (q+2) => (Pi.single i (1 : K) : Fin (q+2) → K)) =
        (Pi.basisFun K (Fin (q+2))) := by
      funext i; simp
    rw [heq]
    exact (Pi.basisFun K (Fin (q+2))).linearIndependent
  exact hbasis.comp Subtype.val Subtype.val_injective

private lemma gradePiece_eq_span_range (q : ℕ) (α : Fin 3) :
    gradePiece K q α = Submodule.span K (Set.range (indFamily (K := K) q α)) := rfl

private lemma finrank_gradePiece (q : ℕ) (α : Fin 3) :
    Module.finrank K (gradePiece K q α) =
      Fintype.card {k : Fin (q+2) // typeOf q k = α} := by
  rw [gradePiece_eq_span_range]
  exact finrank_span_eq_card (indFamily_linearIndependent (K := K) q α)

private lemma card_typeOf_zero : Fintype.card {k : Fin 8 // typeOf 6 k = 0} = 1 := by decide

private lemma card_typeOf_one : Fintype.card {k : Fin 8 // typeOf 6 k = 1} = 6 := by decide

private lemma card_typeOf_two : Fintype.card {k : Fin 8 // typeOf 6 k = 2} = 1 := by decide

private lemma finrank_gradePiece_q6_zero :
    Module.finrank K (gradePiece K 6 0) = 1 := by
  rw [finrank_gradePiece]; exact card_typeOf_zero

private lemma finrank_gradePiece_q6_one :
    Module.finrank K (gradePiece K 6 1) = 6 := by
  rw [finrank_gradePiece]; exact card_typeOf_one

private lemma finrank_gradePiece_q6_two :
    Module.finrank K (gradePiece K 6 2) = 1 := by
  rw [finrank_gradePiece]; exact card_typeOf_two

private lemma G6_dim_zero (i : Fin 3) :
    Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).classOf i 0) = 1 := by
  show Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).decomp i 0) = 1
  match i with
  | ⟨0, _⟩ => exact finrank_gradePiece_q6_zero
  | ⟨1, _⟩ => exact finrank_gradePiece_q6_zero
  | ⟨2, _⟩ => exact finrank_gradePiece_q6_zero

private lemma G6_dim_one (i : Fin 3) :
    Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).classOf i 1) = 6 := by
  show Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).decomp i 1) = 6
  match i with
  | ⟨0, _⟩ => exact finrank_gradePiece_q6_one
  | ⟨1, _⟩ => exact finrank_gradePiece_q6_one
  | ⟨2, _⟩ => exact finrank_gradePiece_q6_one

private lemma G6_dim_two (i : Fin 3) :
    Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).classOf i 2) = 1 := by
  show Module.finrank K
      ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).decomp i 2) = 1
  match i with
  | ⟨0, _⟩ => exact finrank_gradePiece_q6_two
  | ⟨1, _⟩ => exact finrank_gradePiece_q6_two
  | ⟨2, _⟩ => exact finrank_gradePiece_q6_two

/-! ## Support pattern unfolding -/

private lemma sum_CWSupportPattern (f : Fin 3 × Fin 3 × Fin 3 → ℝ) :
    (∑ x ∈ CWSupportPattern, f x) =
      f (0, 1, 1) + f (1, 0, 1) + f (1, 1, 0) +
      f (0, 0, 2) + f (0, 2, 0) + f (2, 0, 0) := by
  show (∑ x ∈ ({(0, 1, 1), (1, 0, 1), (1, 1, 0), (0, 0, 2), (0, 2, 0), (2, 0, 0)} :
            Finset (Fin 3 × Fin 3 × Fin 3)), f x) = _
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private lemma cwSupportPattern_symmetric : LaserSymmetric CWSupportPattern := by
  intro x hx
  fin_cases hx <;> decide

/-! ## Numeric helpers -/

private lemma three_log_five_halves_le_four_log_six :
    3 * Real.log (5/2) ≤ 4 * Real.log 6 := by
  have h3pow : Real.log (((5:ℝ)/2)^3) = 3 * Real.log ((5:ℝ)/2) := by
    rw [Real.log_pow]; push_cast; ring
  have h4pow : Real.log ((6:ℝ)^4) = 4 * Real.log (6 : ℝ) := by
    rw [Real.log_pow]; push_cast; ring
  rw [← h3pow, ← h4pow]
  apply Real.log_le_log
  · positivity
  · norm_num

/-! ## Uniform distribution on CWSupportPattern -/

private noncomputable def uniformDist :
    (Fin 3 × Fin 3 × Fin 3) → ℝ :=
  fun σ => if σ ∈ CWSupportPattern then 1/6 else 0

private lemma uniformDist_nonneg : ∀ σ, 0 ≤ uniformDist σ := by
  intro σ; unfold uniformDist
  split_ifs <;> norm_num

private lemma uniformDist_off (σ : Fin 3 × Fin 3 × Fin 3)
    (h : σ ∉ CWSupportPattern) : uniformDist σ = 0 := by
  unfold uniformDist; rw [if_neg h]

private lemma uniformDist_on (σ : Fin 3 × Fin 3 × Fin 3)
    (h : σ ∈ CWSupportPattern) : uniformDist σ = 1/6 := by
  unfold uniformDist; rw [if_pos h]

private lemma uniformDist_sum_one :
    (∑ σ ∈ CWSupportPattern, uniformDist σ) = 1 := by
  rw [sum_CWSupportPattern]
  have h1 : uniformDist (0, 1, 1) = 1/6 := uniformDist_on _ (by decide)
  have h2 : uniformDist (1, 0, 1) = 1/6 := uniformDist_on _ (by decide)
  have h3 : uniformDist (1, 1, 0) = 1/6 := uniformDist_on _ (by decide)
  have h4 : uniformDist (0, 0, 2) = 1/6 := uniformDist_on _ (by decide)
  have h5 : uniformDist (0, 2, 0) = 1/6 := uniformDist_on _ (by decide)
  have h6 : uniformDist (2, 0, 0) = 1/6 := uniformDist_on _ (by decide)
  rw [h1, h2, h3, h4, h5, h6]; norm_num

/-! ## Generic bounds for the BddAbove proof. -/

private lemma neg_xlogx_le_one (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    -(x * Real.log x) ≤ 1 := by
  rcases eq_or_lt_of_le hx with hx0 | hx0
  · rw [← hx0]; simp
  · have habs : |Real.log x * x| < 1 := Real.abs_log_mul_self_lt x hx0 hx1
    have habs' : |x * Real.log x| < 1 := by rw [mul_comm]; exact habs
    have habs'' := abs_le.mp habs'.le
    linarith

private lemma G6_dim_bd (i : Fin 3) (α : Fin 3) :
    (1 : ℝ) ≤ ((Module.finrank K
        ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).classOf i α) : ℕ) : ℝ) ∧
    ((Module.finrank K
        ((canonicalGrading 6 : (CWObj K 6).TypeGrading 3).classOf i α) : ℕ) : ℝ) ≤ 6 := by
  obtain ⟨α_val, α_lt⟩ := α
  match α_val, α_lt with
  | 0, _ =>
    have h := G6_dim_zero (K := K) i
    have heq : (⟨0, by omega⟩ : Fin 3) = (0 : Fin 3) := rfl
    rw [heq, h]
    refine ⟨by norm_num, by norm_num⟩
  | 1, _ =>
    have h := G6_dim_one (K := K) i
    have heq : (⟨1, by omega⟩ : Fin 3) = (1 : Fin 3) := rfl
    rw [heq, h]
    refine ⟨by norm_num, by norm_num⟩
  | 2, _ =>
    have h := G6_dim_two (K := K) i
    have heq : (⟨2, by omega⟩ : Fin 3) = (2 : Fin 3) := rfl
    rw [heq, h]
    refine ⟨by norm_num, by norm_num⟩

end MMECWLaserWitnessWZSol

open MMECWLaserWitnessWZSol

/-! ## The main proof. -/

set_option maxHeartbeats 800000 in
theorem solution {K : Type u} [Field K] :
    ∃ (G : (CWObj K 6).TypeGrading 3) (S : Finset (Fin 3 × Fin 3 × Fin 3)),
      LaserSymmetric S ∧
      TensorObj.LaserAlignedSupport G S ∧
      (5 : ℝ) / 2 ≤ laserValueFormula_wz G S := by
  classical
  refine ⟨canonicalGrading 6, CWSupportPattern,
    cwSupportPattern_symmetric,
    canonicalGrading_aligned 6, ?_⟩
  set G : (CWObj K 6).TypeGrading 3 := canonicalGrading 6 with hG_def
  set L : ℝ := Real.log 2 with hL_def
  have hL_pos : 0 < L := Real.log_pos (by norm_num)
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  have hdim0 : ∀ i : Fin 3, ((Module.finrank K (G.classOf i 0) : ℕ) : ℝ) = 1 := by
    intro i; rw [G6_dim_zero]; norm_cast
  have hdim1 : ∀ i : Fin 3, ((Module.finrank K (G.classOf i 1) : ℕ) : ℝ) = 6 := by
    intro i; rw [G6_dim_one]; norm_cast
  have hdim2 : ∀ i : Fin 3, ((Module.finrank K (G.classOf i 2) : ℕ) : ℝ) = 1 := by
    intro i; rw [G6_dim_two]; norm_cast
  set Sset : Set ℝ := { v : ℝ |
    ∃ π : (Fin 3 × Fin 3 × Fin 3) → ℝ,
      (∀ σ, σ ∉ CWSupportPattern → π σ = 0) ∧
      (∀ σ, 0 ≤ π σ) ∧
      (∑ σ ∈ CWSupportPattern, π σ) = 1 ∧
      v = Real.exp (Real.log 2 *
        ( (-(∑ σ ∈ CWSupportPattern, π σ * (Real.log (π σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ CWSupportPattern, π σ *
              (Real.log
                  (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) ) ) }
    with hSset_def
  set Vunif : ℝ := Real.exp (Real.log 2 *
        ( (-(∑ σ ∈ CWSupportPattern, uniformDist σ *
              (Real.log (uniformDist σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ CWSupportPattern, uniformDist σ *
              (Real.log
                  (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) )) with hVunif_def
  have hVunif_mem : Vunif ∈ Sset := by
    refine ⟨uniformDist, uniformDist_off, uniformDist_nonneg, uniformDist_sum_one, rfl⟩
  have hVunif_ge : (5 : ℝ) / 2 ≤ Vunif := by
    have hπall : ∀ σ ∈ CWSupportPattern, uniformDist σ = 1/6 := by
      intro σ hσ; exact uniformDist_on σ hσ
    have h_entropy_sum :
        (∑ σ ∈ CWSupportPattern,
            uniformDist σ * (Real.log (uniformDist σ) / Real.log 2)) =
        Real.log (1/6 : ℝ) / Real.log 2 := by
      have h_each : ∀ σ ∈ CWSupportPattern,
          uniformDist σ * (Real.log (uniformDist σ) / Real.log 2) =
          (1/6) * (Real.log ((1:ℝ)/6) / Real.log 2) := by
        intro σ hσ; rw [hπall σ hσ]
      rw [Finset.sum_congr rfl h_each]
      rw [Finset.sum_const]
      have hcard : CWSupportPattern.card = 6 := by decide
      rw [hcard]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    have h_dim_middle : ∀ σ ∈ ({(0,1,1), (1,0,1), (1,1,0)} :
        Finset (Fin 3 × Fin 3 × Fin 3)),
        (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
         ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
         ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)) = 36 := by
      intro σ hσ
      fin_cases hσ
      · rw [hdim0 0, hdim1 1, hdim1 2]; ring
      · rw [hdim1 0, hdim0 1, hdim1 2]; ring
      · rw [hdim1 0, hdim1 1, hdim0 2]; ring
    have h_dim_bound : ∀ σ ∈ ({(0,0,2), (0,2,0), (2,0,0)} :
        Finset (Fin 3 × Fin 3 × Fin 3)),
        (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
         ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
         ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)) = 1 := by
      intro σ hσ
      fin_cases hσ
      · rw [hdim0 0, hdim0 1, hdim2 2]; ring
      · rw [hdim0 0, hdim2 1, hdim0 2]; ring
      · rw [hdim2 0, hdim0 1, hdim0 2]; ring
    have h_dim_sum :
        (∑ σ ∈ CWSupportPattern, uniformDist σ *
              (Real.log
                  (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) = Real.log 6 / Real.log 2 := by
      rw [sum_CWSupportPattern]
      have h011 := h_dim_middle (0,1,1) (by decide)
      have h101 := h_dim_middle (1,0,1) (by decide)
      have h110 := h_dim_middle (1,1,0) (by decide)
      have h002 := h_dim_bound (0,0,2) (by decide)
      have h020 := h_dim_bound (0,2,0) (by decide)
      have h200 := h_dim_bound (2,0,0) (by decide)
      have u011 : uniformDist (0,1,1) = 1/6 := uniformDist_on _ (by decide)
      have u101 : uniformDist (1,0,1) = 1/6 := uniformDist_on _ (by decide)
      have u110 : uniformDist (1,1,0) = 1/6 := uniformDist_on _ (by decide)
      have u002 : uniformDist (0,0,2) = 1/6 := uniformDist_on _ (by decide)
      have u020 : uniformDist (0,2,0) = 1/6 := uniformDist_on _ (by decide)
      have u200 : uniformDist (2,0,0) = 1/6 := uniformDist_on _ (by decide)
      rw [u011, u101, u110, u002, u020, u200, h011, h101, h110, h002, h020, h200]
      rw [Real.log_one]
      have hlog36 : Real.log (36 : ℝ) = 2 * Real.log 6 := by
        have h36 : (36 : ℝ) = 6 * 6 := by norm_num
        rw [h36, Real.log_mul (by norm_num) (by norm_num)]; ring
      rw [hlog36]; field_simp; ring
    have hlog16 : Real.log ((1:ℝ)/6) = -Real.log 6 := by
      rw [Real.log_div one_ne_zero (by norm_num), Real.log_one]; ring
    have h_exp : Real.log 2 *
        ( (-(∑ σ ∈ CWSupportPattern, uniformDist σ *
              (Real.log (uniformDist σ) / Real.log 2)))
        + (1 / 3) *
            (∑ σ ∈ CWSupportPattern, uniformDist σ *
              (Real.log
                  (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                   ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
                / Real.log 2)) ) = (4/3) * Real.log 6 := by
      rw [h_entropy_sum, h_dim_sum, hlog16]
      field_simp
      ring
    have hVunif_eq : Vunif = Real.exp ((4/3) * Real.log 6) := by
      rw [hVunif_def, h_exp]
    rw [hVunif_eq]
    rw [← Real.log_le_iff_le_exp (by norm_num : (0:ℝ) < 5/2)]
    have h_key := three_log_five_halves_le_four_log_six
    linarith
  -- BddAbove with very generous bound `Real.exp 1000`.
  apply le_csSup_of_le _ hVunif_mem hVunif_ge
  refine ⟨Real.exp 1000, ?_⟩
  rintro v ⟨π, hπoff, hπnn, hπsum, rfl⟩
  apply Real.exp_le_exp.mpr
  have hπ_le_one : ∀ σ ∈ CWSupportPattern, π σ ≤ 1 := by
    intro σ hσ
    have h := Finset.single_le_sum (f := π) (fun τ _ => hπnn τ) hσ
    rw [hπsum] at h; exact h
  have hprod_bd : ∀ σ : Fin 3 × Fin 3 × Fin 3,
      (1 : ℝ) ≤ ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
            ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
            ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ) ∧
      ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
            ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
            ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ) ≤ 216 := by
    intro σ
    have ⟨a1, a2⟩ := G6_dim_bd (K := K) 0 σ.1
    have ⟨b1, b2⟩ := G6_dim_bd (K := K) 1 σ.2.1
    have ⟨c1, c2⟩ := G6_dim_bd (K := K) 2 σ.2.2
    have a0 : (0:ℝ) ≤ ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) := by linarith
    have b0 : (0:ℝ) ≤ ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) := by linarith
    have c0 : (0:ℝ) ≤ ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ) := by linarith
    refine ⟨?_, ?_⟩
    · have hab : 1 ≤ ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
          ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) := by
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ _ := mul_le_mul a1 b1 (by linarith) (by linarith)
      calc (1:ℝ) = 1 * 1 := by ring
        _ ≤ _ := mul_le_mul hab c1 (by linarith) (by nlinarith)
    · have hab : ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
          ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) ≤ 36 := by
        have := mul_le_mul a2 b2 b0 (by linarith : (0:ℝ) ≤ 6)
        linarith
      have hab0 : (0:ℝ) ≤ ((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
          ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) := by positivity
      have := mul_le_mul hab c2 c0 (by linarith : (0:ℝ) ≤ 36)
      linarith
  have hlog_216_lt : Real.log 216 < 215 := by
    have := Real.log_lt_sub_one_of_pos (x := (216:ℝ)) (by norm_num) (by norm_num)
    linarith
  have h_entropy_bd :
      -(∑ σ ∈ CWSupportPattern, π σ * Real.log (π σ)) ≤ 6 := by
    rw [← Finset.sum_neg_distrib]
    calc (∑ σ ∈ CWSupportPattern, -(π σ * Real.log (π σ)))
        ≤ ∑ σ ∈ CWSupportPattern, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intros σ hσ
          exact neg_xlogx_le_one (π σ) (hπnn σ) (hπ_le_one σ hσ)
      _ = (CWSupportPattern.card : ℝ) * 1 := by
          rw [Finset.sum_const]
          simp [nsmul_eq_mul]
      _ = 6 := by
          have : CWSupportPattern.card = 6 := by decide
          rw [this]; norm_num
  have h_dim_bd :
      (∑ σ ∈ CWSupportPattern, π σ *
        Real.log
          (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) ≤ 215 := by
    calc (∑ σ ∈ CWSupportPattern, π σ *
        Real.log
          (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)))
        ≤ ∑ σ ∈ CWSupportPattern, π σ * 215 := by
          apply Finset.sum_le_sum
          intros σ hσ
          have ⟨h1, h2⟩ := hprod_bd σ
          have hlog : Real.log
              (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)) ≤ Real.log 216 := by
            apply Real.log_le_log
            · linarith
            · exact h2
          have hlog215 : Real.log
              (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ)) ≤ 215 := by
            linarith
          exact mul_le_mul_of_nonneg_left hlog215 (hπnn σ)
      _ = 215 * (∑ σ ∈ CWSupportPattern, π σ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          ring
      _ = 215 * 1 := by rw [hπsum]
      _ = 215 := by ring
  have hineq : -(∑ σ ∈ CWSupportPattern, π σ * Real.log (π σ)) +
      (1/3) * (∑ σ ∈ CWSupportPattern, π σ *
        Real.log
          (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) ≤ 1000 := by
    have h_third_bd : (1/3 : ℝ) * (∑ σ ∈ CWSupportPattern, π σ *
        Real.log
          (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) ≤ (1/3) * 215 := by
      apply mul_le_mul_of_nonneg_left h_dim_bd (by norm_num : (0:ℝ) ≤ 1/3)
    linarith
  have hL_distr : Real.log 2 *
        (-(∑ σ ∈ CWSupportPattern, π σ * (Real.log (π σ) / Real.log 2)) +
         (1/3) * (∑ σ ∈ CWSupportPattern, π σ *
            (Real.log
                (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
              / Real.log 2))) =
      -(∑ σ ∈ CWSupportPattern, π σ * Real.log (π σ)) +
      (1/3) * (∑ σ ∈ CWSupportPattern, π σ *
        Real.log
          (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
           ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) := by
    have hsum1 : Real.log 2 *
        (-(∑ σ ∈ CWSupportPattern, π σ * (Real.log (π σ) / Real.log 2))) =
        -(∑ σ ∈ CWSupportPattern, π σ * Real.log (π σ)) := by
      rw [mul_neg]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros σ _; field_simp
    have hsum2_inner :
        Real.log 2 * (∑ σ ∈ CWSupportPattern, π σ *
            (Real.log
                (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
              / Real.log 2)) =
        (∑ σ ∈ CWSupportPattern, π σ *
            Real.log
              (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros σ _; field_simp
    have hsum2 : Real.log 2 *
        ((1/3) * (∑ σ ∈ CWSupportPattern, π σ *
            (Real.log
                (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
                 ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))
              / Real.log 2))) =
        (1/3) * (∑ σ ∈ CWSupportPattern, π σ *
            Real.log
              (((Module.finrank K (G.classOf 0 σ.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 1 σ.2.1) : ℕ) : ℝ) *
               ((Module.finrank K (G.classOf 2 σ.2.2) : ℕ) : ℝ))) := by
      have := hsum2_inner
      linarith [this]
    linarith [hsum1, hsum2]
  rw [hL_distr]
  exact hineq
