-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter16
-- name    : ProofsInTheBook_Chapter16
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T15:12:54.054952+00:00
-- url     : https://prove2.me/theorems/774c63fa-f0db-48d9-9182-7f9984c0f15c
-- title:
--   Borsuk counterexample constructions in dimension 1325
-- statement:
--   The bundle defines Borsuk's covering property in Euclidean dimension $d$: every bounded set of positive diameter admits a cover by $d+1$ subsets of itself, each with strictly smaller diameter. A Kahn–Kalai certificate contains a set violating that property, together with proofs of boundedness, positive diameter, and the covering obstruction. The retained finite-set, cut-incidence, and Euclidean constructions include a proved certificate in dimension $1325$.
-- source:
--   Existing Lean formalization associated with Aigner and Ziegler, Proofs from THE BOOK. Repository chapter 16; repository numbering is not an edition-specific book chapter number. Exact source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter16.lean

import Mathlib

/-!
# Chapter 16: Borsuk's conjecture

From "Proofs from THE BOOK":

**Borsuk's conjecture**: Can every bounded set in ℝ^d be partitioned
into d+1 parts, each of smaller diameter? Borsuk conjectured yes (1933).

The book discusses the conjecture and its Kahn-Kalai (1993) disproof in
dimension `1325`.  The later `d ≥ 298` bound is due to Hinrichs-Richter
(2003) and uses a different construction.

Formalization status: this file defines finite color-class bookkeeping, states
the corrected `BorsukConjecture d` for covers of a bounded set by subsets of
itself in `EuclideanSpace ℝ (Fin d)`, packages a counterexample as
`KahnKalaiCertificate d`, and formalizes enough of the
Frankl-Wilson/Kahn-Kalai pipeline to prove the unconditional `chapter16`
statement.  The local construction currently proves an explicit counterexample
in the book's Kahn-Kalai dimension `d = 1325`, using the fixed-layer `p = 13`
Frankl-Wilson bound, the unordered cut-vector realization, and its
codimension-one zero-sum hyperplane reduction.  The earlier pointed `p = 17`
construction remains available as scaffolding and gives `4624 ≤ d ≤ 6848`.
Mathlib has Euclidean metric spaces and finite-set tools, but not this
Frankl-Wilson/Kahn-Kalai pipeline as an available theorem.

TODO (future): formalize the Hinrichs-Richter (2003) construction to reach d ≥ 298; needs a separate 2-distance-set / strongly-regular-graph construction not in the book's proof.

Mathlib search status (2026-05-24): no Frankl-Wilson theorem, modular
intersection theorem, Ray-Chaudhuri-Wilson theorem, or oddtown/eventown theorem
was present under those names or nearby combinatorial names.  The local
additions below provide the reusable diagonal-functional linear independence
core, its mod-2 oddtown specialization, and the prime modular-intersection
form needed by the pointed Kahn-Kalai construction.
-/

namespace ProofsInTheBook.Chapter16



























/--
Linear-algebra core used by Frankl-Wilson style arguments: a family of vectors
is linearly independent if there are linear functionals whose evaluation matrix
is diagonal with nonzero diagonal.
-/
theorem linearIndependent_of_linear_functionals_diagonal
    {K : Type*} [Field K] {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module K M] (v : ι → M) (φ : ι → M →ₗ[K] K)
    (hdiag : ∀ i, φ i (v i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → φ i (v j) = 0) :
    LinearIndependent K v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have happly : φ i (∑ j, g j • v j) = φ i 0 := congrArg (fun x => φ i x) hsum
  simp only [map_sum, map_smul, map_zero] at happly
  have hsingle : (∑ j, g j • φ i (v j)) = g i • φ i (v i) := by
    rw [Finset.sum_eq_single i]
    · intro j _ hji
      rw [hoff i j hji.symm]
      simp
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsingle] at happly
  have hmul : g i * φ i (v i) = 0 := by simpa [smul_eq_mul] using happly
  exact (mul_eq_zero.mp hmul).resolve_right (hdiag i)

/-- Dimension bound form of `linearIndependent_of_linear_functionals_diagonal`. -/
theorem fintype_card_le_finrank_of_linear_functionals_diagonal
    {K : Type*} [Field K] {ι M : Type*} [Fintype ι]
    [AddCommGroup M] [Module K M] [Module.Finite K M]
    (v : ι → M) (φ : ι → M →ₗ[K] K)
    (hdiag : ∀ i, φ i (v i) ≠ 0)
    (hoff : ∀ i j, i ≠ j → φ i (v j) = 0) :
    Fintype.card ι ≤ Module.finrank K M :=
  (linearIndependent_of_linear_functionals_diagonal v φ hdiag hoff).fintype_card_le_finrank











/-- Boolean monomial on finite subsets: it evaluates to `1` exactly when `I ⊆ X`. -/
def subsetMonomial (K : Type*) [Zero K] [One K] {α : Type*} [DecidableEq α]
    (I : Finset α) : Finset α → K :=
  fun X => if I ⊆ X then 1 else 0

/--
The subspace of Boolean functions spanned by monomials of degree at most `r`.
This is the direct set-family substitute for the low-degree multilinear
polynomial space in the Frankl-Wilson proof.
-/
def lowDegreeBooleanSubmodule (K : Type*) [Field K] (α : Type*) [Fintype α]
    [DecidableEq α] (r : ℕ) : Submodule K (Finset α → K) :=
  Submodule.span K
    (Set.range (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1))

theorem subsetMonomial_mem_lowDegree {K α : Type*} [Field K] [Fintype α] [DecidableEq α]
    {r : ℕ} {I : Finset α} (hI : I.card ≤ r) :
    subsetMonomial K I ∈ lowDegreeBooleanSubmodule K α r :=
  Submodule.subset_span ⟨⟨I, hI⟩, rfl⟩



theorem sum_subsetMonomial_insert_apply {K α : Type*} [Field K] [DecidableEq α]
    (A I X : Finset α) :
    (∑ a ∈ A, subsetMonomial K (insert a I) X) =
      ((A ∩ X).card : K) * subsetMonomial K I X := by
  by_cases hIX : I ⊆ X
  · have h_insert_iff : ∀ a, insert a I ⊆ X ↔ a ∈ X := by
      intro a
      constructor
      · intro h
        exact h (Finset.mem_insert_self a I)
      · intro ha x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact hIX hx
    rw [Finset.card_eq_sum_ones]
    simp [subsetMonomial, hIX, h_insert_iff]
  · have h_insert_false : ∀ a, ¬ insert a I ⊆ X := by
      intro a h
      exact hIX ((Finset.subset_insert a I).trans h)
    simp [subsetMonomial, hIX, h_insert_false]

/-- Multiply a Boolean function by the affine intersection-count factor `|A ∩ X| - c`. -/
def booleanIntersectionFactor (K : Type*) [Field K] {α : Type*} [DecidableEq α]
    (A : Finset α) (c : K) : (Finset α → K) →ₗ[K] (Finset α → K) where
  toFun f := fun X => (((A ∩ X).card : K) - c) * f X
  map_add' f g := by
    ext X
    simp [mul_add]
  map_smul' c' f := by
    ext X
    simp only [Pi.smul_apply, RingHom.id_apply]
    ring

/--
The basic multilinearization identity: multiplying a monomial by `|A ∩ X| - c`
is a linear combination of monomials whose supports have grown by at most one.
-/
theorem booleanIntersectionFactor_subsetMonomial {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] (A I : Finset α) (c : K) :
    booleanIntersectionFactor K A c (subsetMonomial K I) =
      (∑ a ∈ A, subsetMonomial K (insert a I)) - c • subsetMonomial K I := by
  ext X
  simp only [booleanIntersectionFactor, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply,
    Pi.smul_apply, Finset.sum_apply]
  rw [sum_subsetMonomial_insert_apply (K := K) A I X]
  ring

/--
One Frankl-Wilson factor raises Boolean degree by at most one.  Iterating this
will put the usual product of forbidden-residue factors in the expected
low-degree space.
-/
theorem booleanIntersectionFactor_mem_lowDegree_succ {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {r : ℕ} {A : Finset α} {c : K} {f : Finset α → K}
    (hf : f ∈ lowDegreeBooleanSubmodule K α r) :
    booleanIntersectionFactor K A c f ∈ lowDegreeBooleanSubmodule K α (r + 1) := by
  let target := lowDegreeBooleanSubmodule K α (r + 1)
  change booleanIntersectionFactor K A c f ∈ target
  refine Submodule.span_induction (s := Set.range
      (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨I, rfl⟩
    rw [booleanIntersectionFactor_subsetMonomial]
    apply target.sub_mem
    · apply Submodule.sum_mem
      intro a _ha
      exact subsetMonomial_mem_lowDegree (K := K) (α := α)
        ((Finset.card_insert_le a I.1).trans (Nat.succ_le_succ I.2))
    · exact target.smul_mem c
        (subsetMonomial_mem_lowDegree (K := K) (α := α) (I.2.trans (Nat.le_succ r)))
  · simp
  · intro x y _ _ hx hy
    simpa using target.add_mem hx hy
  · intro a x _ hx
    simpa using target.smul_mem a hx

/--
The Frankl-Wilson product attached to a set `A` and a finite set of forbidden
field values.  On a Boolean input `X`, this is
`∏ c ∈ L, (|A ∩ X| - c)`.
-/
def franklWilsonFunction (K : Type*) [Field K] {α : Type*} [DecidableEq α]
    (A : Finset α) (L : Finset K) : Finset α → K :=
  fun X => ∏ c ∈ L, (((A ∩ X).card : K) - c)

theorem franklWilsonFunction_insert {K α : Type*} [Field K] [DecidableEq K]
    [DecidableEq α] {c : K} {L : Finset K} (hc : c ∉ L) (A : Finset α) :
    franklWilsonFunction K A (insert c L) =
      booleanIntersectionFactor K A c (franklWilsonFunction K A L) := by
  ext X
  simp [franklWilsonFunction, booleanIntersectionFactor, hc, mul_comm]

/--
The Frankl-Wilson product has Boolean degree at most the number of forbidden
values.  This is the low-degree half of the modular intersection theorem.
-/
theorem franklWilsonFunction_mem_lowDegree {K α : Type*} [Field K] [Fintype α]
    [DecidableEq K] [DecidableEq α] (A : Finset α) (L : Finset K) :
    franklWilsonFunction K A L ∈ lowDegreeBooleanSubmodule K α L.card := by
  induction L using Finset.induction_on with
  | empty =>
      simpa [franklWilsonFunction, subsetMonomial] using
        (subsetMonomial_mem_lowDegree (K := K) (α := α) (I := (∅ : Finset α)) (r := 0)
          (by simp))
  | insert c L hc hL =>
      rw [franklWilsonFunction_insert (K := K) (α := α) hc A]
      have hmem := booleanIntersectionFactor_mem_lowDegree_succ (K := K) (α := α)
        (A := A) (c := c) (f := franklWilsonFunction K A L) hL
      simpa [Finset.card_insert_of_notMem hc] using hmem





/-- The fixed-card slice of the Boolean cube. -/
abbrev FixedCardSubsets (α : Type*) [Fintype α] [DecidableEq α] (q : ℕ) :=
  {X : Finset α // X.card = q}

/-- A Boolean monomial restricted to the fixed-card slice. -/
def sliceSubsetMonomial (K : Type*) [Zero K] [One K] {α : Type*} [Fintype α]
    [DecidableEq α] {q : ℕ} (I : Finset α) : FixedCardSubsets α q → K :=
  fun X => subsetMonomial K I X.1

/--
On the fixed-card slice, monomials of degree at most `r` are spanned by
monomials of exact degree `r`, provided the relevant binomial coefficients are
nonzero in the field.
-/
def exactDegreeSliceSubmodule (K : Type*) [Field K] (α : Type*) [Fintype α]
    [DecidableEq α] (q r : ℕ) : Submodule K (FixedCardSubsets α q → K) :=
  Submodule.span K
    (Set.range (fun I : {I : Finset α // I.card = r} =>
      sliceSubsetMonomial K (q := q) I.1))

theorem exactDegreeSliceSubmodule_finrank_le
    (K α : Type*) [Field K] [Fintype α] [DecidableEq α] (q r : ℕ) :
    Module.finrank K (exactDegreeSliceSubmodule K α q r) ≤
      Fintype.card {I : Finset α // I.card = r} :=
  finrank_range_le_card (R := K) (M := FixedCardSubsets α q → K)
    (b := fun I : {I : Finset α // I.card = r} =>
      sliceSubsetMonomial K (q := q) I.1)

theorem sum_exact_slice_monomials_of_subset {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} (I : Finset α) (hIr : I.card ≤ r) :
    (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
        sliceSubsetMonomial K (q := q) J) =
      ((q - I.card).choose (r - I.card) : K) • sliceSubsetMonomial K (q := q) I := by
  ext X
  simp only [Finset.sum_apply]
  dsimp [sliceSubsetMonomial, subsetMonomial]
  by_cases hIX : I ⊆ X.1
  · have hleft_filter :
        ((Finset.univ : Finset α).powersetCard r).filter (fun J => I ⊆ J ∧ J ⊆ X.1) =
          (X.1.powersetCard r).filter (fun J => I ⊆ J) := by
      ext J
      simp [Finset.mem_powersetCard]
      aesop
    have hcard :
        (((Finset.univ : Finset α).powersetCard r).filter
            (fun J => I ⊆ J ∧ J ⊆ X.1)).card =
          (q - I.card).choose (r - I.card) := by
      rw [hleft_filter, Finset.card_filter_powersetCard_subset I X.1 r hIX hIr, X.2]
    rw [if_pos hIX]
    rw [← hcard]
    rw [← Finset.sum_boole (R := K) (s := (Finset.univ : Finset α).powersetCard r)
      (p := fun J => I ⊆ J ∧ J ⊆ X.1)]
    rw [Finset.sum_filter]
    rw [mul_one]
    apply Finset.sum_congr rfl
    intro J _hJ
    by_cases hIJ : I ⊆ J <;> by_cases hJX : J ⊆ X.1 <;> simp [hIJ, hJX]
  · have hzero :
        (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
            if J ⊆ X.1 then (1 : K) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro J hJ
      rw [Finset.mem_filter] at hJ
      have hJXfalse : ¬ J ⊆ X.1 := by
        intro hJX
        exact hIX (hJ.2.trans hJX)
      simp [hJXfalse]
    rw [if_neg hIX]
    simpa using hzero

theorem sliceSubsetMonomial_mem_exact_of_card_le {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} {I : Finset α} (hIr : I.card ≤ r)
    (hcoeff : ((q - I.card).choose (r - I.card) : K) ≠ 0) :
    sliceSubsetMonomial K (q := q) I ∈ exactDegreeSliceSubmodule K α q r := by
  let target := exactDegreeSliceSubmodule K α q r
  have hsum_mem :
      (∑ J ∈ (Finset.univ : Finset α).powersetCard r with I ⊆ J,
          sliceSubsetMonomial K (q := q) J) ∈ target := by
    apply Submodule.sum_mem
    intro J hJ
    rw [Finset.mem_filter] at hJ
    have hJcard : J.card = r := (Finset.mem_powersetCard.mp hJ.1).2
    exact Submodule.subset_span ⟨⟨J, hJcard⟩, rfl⟩
  have hscaled : ((q - I.card).choose (r - I.card) : K) •
      sliceSubsetMonomial K (q := q) I ∈ target := by
    simpa [target] using (by
      rw [← sum_exact_slice_monomials_of_subset (K := K) (q := q) I hIr]
      exact hsum_mem)
  exact (target.smul_mem_iff hcoeff).mp hscaled

theorem lowDegree_restrict_mem_exact {K α : Type*} [Field K] [Fintype α]
    [DecidableEq α] {q r : ℕ} {f : Finset α → K}
    (hcoeff : ∀ I : Finset α, I.card ≤ r →
      ((q - I.card).choose (r - I.card) : K) ≠ 0)
    (hf : f ∈ lowDegreeBooleanSubmodule K α r) :
    (fun X : FixedCardSubsets α q => f X.1) ∈ exactDegreeSliceSubmodule K α q r := by
  let target := exactDegreeSliceSubmodule K α q r
  change (fun X : FixedCardSubsets α q => f X.1) ∈ target
  refine Submodule.span_induction (s := Set.range
      (fun I : {I : Finset α // I.card ≤ r} => subsetMonomial K I.1)) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨I, rfl⟩
    change sliceSubsetMonomial K (q := q) I.1 ∈ target
    exact sliceSubsetMonomial_mem_exact_of_card_le (K := K) (α := α) (q := q) I.2
      (hcoeff I.1 I.2)
  · exact target.zero_mem
  · intro x y _ _ hx hy
    simpa using target.add_mem hx hy
  · intro a x _ hx
    simpa using target.smul_mem a hx

/-- Evaluation at a point of the fixed-card slice. -/
def fixedEvalLinear (K : Type*) [Semiring K] {α : Type*} [Fintype α] [DecidableEq α]
    {q : ℕ} (X : FixedCardSubsets α q) : (FixedCardSubsets α q → K) →ₗ[K] K where
  toFun f := f X
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/--
Frankl-Wilson bound sharpened on a fixed-card slice: the low-degree space can
be replaced by exact-degree monomials.
-/
theorem franklWilson_fixed_card_modular_intersection_bound
    {K α ι : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K] [Fintype ι]
    {q : ℕ} (sets : ι → Finset α) (L : Finset K)
    (hcard : ∀ i, (sets i).card = q)
    (hcoeff : ∀ I : Finset α, I.card ≤ L.card →
      ((q - I.card).choose (L.card - I.card) : K) ≠ 0)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hinter : ∀ i j, i ≠ j → (((sets i ∩ sets j).card : K) ∈ L)) :
    Fintype.card ι ≤ Fintype.card {I : Finset α // I.card = L.card} := by
  let target := exactDegreeSliceSubmodule K α q L.card
  let v : ι → target := fun i =>
    ⟨fun X : FixedCardSubsets α q => franklWilsonFunction K (sets i) L X.1,
      lowDegree_restrict_mem_exact (K := K) (α := α) (q := q) (r := L.card)
        hcoeff (franklWilsonFunction_mem_lowDegree (K := K) (α := α) (sets i) L)⟩
  let φ : ι → target →ₗ[K] K := fun i =>
    (fixedEvalLinear K ⟨sets i, hcard i⟩).comp target.subtype
  have hdiag : ∀ i, φ i (v i) ≠ 0 := by
    intro i
    dsimp [φ, v, fixedEvalLinear]
    rw [franklWilsonFunction, Finset.inter_self]
    change (∏ x ∈ L, (((sets i).card : K) - x)) ≠ 0
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [sub_ne_zero]
    intro h
    exact hself i (by simpa [h] using hc)
  have hoff : ∀ i j, i ≠ j → φ i (v j) = 0 := by
    intro i j hij
    dsimp [φ, v, fixedEvalLinear]
    rw [franklWilsonFunction]
    exact Finset.prod_eq_zero (hinter j i hij.symm) (by simp)
  have hcard_le_finrank : Fintype.card ι ≤ Module.finrank K target :=
    fintype_card_le_finrank_of_linear_functionals_diagonal v φ hdiag hoff
  exact hcard_le_finrank.trans (exactDegreeSliceSubmodule_finrank_le K α q L.card)

/-- Count fixed-card subsets of a finite type. -/
theorem exactSubsets_card_eq_choose {α : Type*} [Fintype α] [DecidableEq α] (r : ℕ) :
    Fintype.card {I : Finset α // I.card = r} = (Fintype.card α).choose r := by
  rw [Fintype.card_subtype]
  have hset : ({I : Finset α | I.card = r} : Finset (Finset α)) =
      (Finset.univ : Finset α).powersetCard r := by
    ext I
    simp [Finset.mem_powersetCard]
  rw [hset, Finset.card_powersetCard, Finset.card_univ]

/--
Coloring form of the fixed-card Frankl-Wilson bound.
-/
theorem exists_monochromatic_pair_fixed_card_intersection_notMem
    {K α ι κ : Type*} [Field K] [Fintype α] [DecidableEq α] [DecidableEq K]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {q : ℕ} (sets : ι → Finset α) (L : Finset K) (color : ι → κ)
    (hcard : ∀ i, (sets i).card = q)
    (hcoeff : ∀ I : Finset α, I.card ≤ L.card →
      ((q - I.card).choose (L.card - I.card) : K) ≠ 0)
    (hself : ∀ i, ((sets i).card : K) ∉ L)
    (hlarge :
      Fintype.card κ * Fintype.card {I : Finset α // I.card = L.card} < Fintype.card ι) :
    ∃ i j, i ≠ j ∧ color i = color j ∧ (((sets i ∩ sets j).card : K) ∉ L) := by
  obtain ⟨c, hc⟩ := Fintype.exists_lt_card_fiber_of_mul_lt_card color hlarge
  rw [← Fintype.card_subtype (fun i : ι => color i = c)] at hc
  let fiber := {i : ι // color i = c}
  let restrictedSets : fiber → Finset α := fun i => sets i.1
  have hcard_fiber : ∀ i : fiber, (restrictedSets i).card = q := by
    intro i
    exact hcard i.1
  have hself_fiber : ∀ i : fiber, ((restrictedSets i).card : K) ∉ L := by
    intro i
    exact hself i.1
  by_contra hno
  push Not at hno
  have hinter_fiber :
      ∀ i j : fiber, i ≠ j → (((restrictedSets i ∩ restrictedSets j).card : K) ∈ L) := by
    intro i j hij
    simpa [restrictedSets] using
      hno i.1 j.1 (fun h => hij (Subtype.ext h)) (i.2.trans j.2.symm)
  have hle :=
    franklWilson_fixed_card_modular_intersection_bound restrictedSets L hcard_fiber hcoeff
      hself_fiber hinter_fiber
  exact (not_lt_of_ge hle) hc






/--
The Hamming distance between two finite subsets of a finite ground type,
counted as the number of coordinates where their membership indicators differ.
-/
def finsetSymmDiffSet {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : Finset α :=
  Finset.univ.filter fun a => (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A)

def finsetSymmDiffCard {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) : ℕ :=
  (finsetSymmDiffSet A B).card

theorem mem_finsetSymmDiffSet_iff {α : Type*} [Fintype α] [DecidableEq α]
    {A B : Finset α} {a : α} :
    a ∈ finsetSymmDiffSet A B ↔ (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A) := by
  simp [finsetSymmDiffSet]

theorem finsetSymmDiffSet_eq_sdiff_union_sdiff
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    finsetSymmDiffSet A B = (A \ B) ∪ (B \ A) := by
  ext a
  simp [finsetSymmDiffSet]

theorem finsetSymmDiffCard_eq_card_sdiff_add_card_sdiff
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    finsetSymmDiffCard A B = (A \ B).card + (B \ A).card := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet_eq_sdiff_union_sdiff]
  rw [Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro a ha hb
  simp at ha hb
  exact ha.2 hb.1

theorem finsetSymmDiffCard_eq_two_mul_sub_inter_of_card_eq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {r : ℕ}
    (hA : A.card = r) (hB : B.card = r) :
    finsetSymmDiffCard A B = 2 * (r - (A ∩ B).card) := by
  rw [finsetSymmDiffCard_eq_card_sdiff_add_card_sdiff]
  have hAB := Finset.card_sdiff_add_card_inter (s := B) (t := A)
  have hBA := Finset.card_sdiff_add_card_inter (s := A) (t := B)
  rw [Finset.inter_comm B A] at hAB
  omega









/-- The directed cut induced by a finite subset of the vertex set. -/
def directedCutSet {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : Finset (α × α) :=
  Finset.univ.filter fun e => (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)







/-- The number of ordered crossing pairs for a cut. -/
theorem directedCutSet_card {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    (directedCutSet A).card = 2 * A.card * (Fintype.card α - A.card) := by
  rw [directedCutSet]
  have hset :
      (Finset.univ.filter fun e : α × α =>
          (e.1 ∈ A ∧ e.2 ∉ A) ∨ (e.1 ∉ A ∧ e.2 ∈ A)) =
        (A ×ˢ Aᶜ) ∪ (Aᶜ ×ˢ A) := by
    ext e
    simp
  rw [hset]
  have hdisj : Disjoint (A ×ˢ Aᶜ) (Aᶜ ×ˢ A) := by
    rw [Finset.disjoint_product]
    exact Or.inl disjoint_compl_right
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_product, Finset.card_product,
    Finset.card_compl]
  ring

/-- The type of unordered non-loop edges on a vertex type. -/
abbrev UndirectedEdge (α : Type*) := {e : Sym2 α // ¬ e.IsDiag}

/-- The complete bipartite cut graph determined by `A`. -/
def cutGraph {α : Type*} [DecidableEq α] (A : Finset α) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => x ∈ A ∧ y ∉ A

/-- The unordered cut as a finite set of non-loop edges. -/
noncomputable def undirectedCutSet {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) : Finset (UndirectedEdge α) := by
  classical
  exact Finset.univ.filter fun e => e.1 ∈ (cutGraph A).edgeSet

theorem mem_undirectedCutSet_iff {α : Type*} [Fintype α] [DecidableEq α]
    {A : Finset α} {e : UndirectedEdge α} :
    e ∈ undirectedCutSet A ↔ e.1 ∈ (cutGraph A).edgeSet := by
  classical
  simp [undirectedCutSet]

noncomputable def cutEdgeSubtypeEquiv {α : Type*} [DecidableEq α] (G : SimpleGraph α) :
    {e : UndirectedEdge α // e.1 ∈ G.edgeSet} ≃ G.edgeSet where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, SimpleGraph.not_isDiag_of_mem_edgeSet G e.2⟩, e.2⟩
  left_inv := by
    rintro ⟨⟨e, _hdiag⟩, _hedge⟩
    rfl
  right_inv := by
    rintro ⟨e, _hedge⟩
    rfl

/-- The unordered cut has `|A| * |Aᶜ|` edges. -/
theorem undirectedCutSet_card {α : Type*} [Fintype α] [DecidableEq α] (A : Finset α) :
    (undirectedCutSet A).card = A.card * (Fintype.card α - A.card) := by
  classical
  let G := cutGraph A
  letI : Fintype G.edgeSet := G.fintypeEdgeSet
  have htwo := SimpleGraph.two_mul_card_edgeFinset G
  rw [SimpleGraph.edgeFinset_card] at htwo
  have hdir : ({x : α × α | G.Adj x.1 x.2} : Finset (α × α)).card =
      (directedCutSet A).card := by
    apply congrArg Finset.card
    rw [directedCutSet]
    ext e
    simp [G, cutGraph]
    constructor
    · intro h
      rcases h.2 with hxy | hyx
      · exact Or.inl hxy
      · exact Or.inr ⟨hyx.2, hyx.1⟩
    · intro h
      refine ⟨?_, ?_⟩
      · intro heq
        rcases h with hxy | hyx
        · exact hxy.2 (by simpa [heq] using hxy.1)
        · exact hyx.1 (by simpa [heq] using hyx.2)
      · rcases h with hxy | hyx
        · exact Or.inl hxy
        · exact Or.inr ⟨hyx.2, hyx.1⟩
  rw [hdir, directedCutSet_card] at htwo
  have hGcard : Fintype.card G.edgeSet = A.card * (Fintype.card α - A.card) := by
    have htwo' : 2 * Fintype.card G.edgeSet =
        2 * (A.card * (Fintype.card α - A.card)) := by
      simpa [mul_assoc] using htwo
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) htwo'
  have hsubCard :
      Fintype.card {e : UndirectedEdge α // e.1 ∈ G.edgeSet} = (undirectedCutSet A).card := by
    exact Fintype.card_ofFinset (undirectedCutSet A) (by
      intro e
      change e ∈ undirectedCutSet A ↔ e.1 ∈ G.edgeSet
      simp [undirectedCutSet, G])
  rw [← hsubCard]
  rw [Fintype.card_congr (cutEdgeSubtypeEquiv G)]
  exact hGcard

theorem undirectedCutSet_symmDiffSet_eq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffSet (undirectedCutSet A) (undirectedCutSet B) =
      undirectedCutSet (finsetSymmDiffSet A B) := by
  classical
  ext e
  rw [mem_finsetSymmDiffSet_iff]
  simp only [mem_undirectedCutSet_iff]
  obtain ⟨z, _hz⟩ := e
  obtain ⟨⟨x, y⟩, hxy⟩ := Quot.exists_rep z
  subst z
  simp [cutGraph, finsetSymmDiffSet]
  tauto

theorem undirectedCutSet_symmDiffCard {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) =
      finsetSymmDiffCard A B * (Fintype.card α - finsetSymmDiffCard A B) := by
  rw [finsetSymmDiffCard, undirectedCutSet_symmDiffSet_eq, undirectedCutSet_card,
    finsetSymmDiffCard]

theorem undirectedCutSet_symmDiffCard_of_card_eq
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {r : ℕ}
    (hA : A.card = r) (hB : B.card = r) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) =
      (2 * (r - (A ∩ B).card)) *
        (Fintype.card α - 2 * (r - (A ∩ B).card)) := by
  rw [undirectedCutSet_symmDiffCard,
    finsetSymmDiffCard_eq_two_mul_sub_inter_of_card_eq A B hA hB]

theorem undirectedCutSet_symmDiffCard_of_kahnKalai_intersection
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) {k : ℕ}
    (hground : Fintype.card α = 4 * k)
    (hA : A.card = 2 * k) (hB : B.card = 2 * k)
    (hinter : (A ∩ B).card = k) :
    finsetSymmDiffCard (undirectedCutSet A) (undirectedCutSet B) = 4 * k * k := by
  rw [undirectedCutSet_symmDiffCard_of_card_eq A B hA hB, hground, hinter]
  have hsub : 2 * k - k = k := by omega
  rw [hsub]
  have hsub' : 4 * k - 2 * k = 2 * k := by omega
  rw [hsub']
  ring





/-- The `0/1` incidence vector of a finite set, viewed as a Euclidean point. -/
noncomputable def realIncidencePoint {α : Type*} [DecidableEq α]
    (A : Finset α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 fun a => if a ∈ A then (1 : ℝ) else 0

@[simp]
theorem realIncidencePoint_apply {α : Type*} [DecidableEq α]
    (A : Finset α) (a : α) :
    realIncidencePoint A a = if a ∈ A then (1 : ℝ) else 0 :=
  rfl

theorem sum_sq_indicator_sub_eq_finsetSymmDiffCard
    {α : Type*} [Fintype α] [DecidableEq α] (A B : Finset α) :
    (∑ a : α, ((if a ∈ A then (1 : ℝ) else 0) -
        (if a ∈ B then (1 : ℝ) else 0)) ^ 2) =
      (finsetSymmDiffCard A B : ℝ) := by
  rw [finsetSymmDiffCard, finsetSymmDiffSet]
  rw [← Finset.sum_boole (R := ℝ) (s := Finset.univ)
    (p := fun a => (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A))]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

/--
The squared Euclidean distance between incidence vectors is the Hamming
distance of the underlying sets.
-/
theorem realIncidencePoint_dist_sq {α : Type*} [Fintype α] [DecidableEq α]
    (A B : Finset α) :
    dist (realIncidencePoint A) (realIncidencePoint B) ^ 2 =
      (finsetSymmDiffCard A B : ℝ) := by
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq]
  rw [PiLp.inner_apply]
  trans ∑ a : α, ((if a ∈ A then (1 : ℝ) else 0) -
      (if a ∈ B then (1 : ℝ) else 0)) ^ 2
  · apply Finset.sum_congr rfl
    intro a _
    simp [pow_two]
  · exact sum_sq_indicator_sub_eq_finsetSymmDiffCard A B



























theorem dist_le_sqrt_of_dist_sq_le {X : Type*} [PseudoMetricSpace X]
    {x y : X} {R : ℝ} (hR : 0 ≤ R) (h : dist x y ^ 2 ≤ R) :
    dist x y ≤ Real.sqrt R :=
  (Real.le_sqrt dist_nonneg hR).2 h

theorem dist_eq_sqrt_of_dist_sq_eq {X : Type*} [PseudoMetricSpace X]
    {x y : X} {R : ℝ} (hR : 0 ≤ R) (h : dist x y ^ 2 = R) :
    dist x y = Real.sqrt R := by
  apply le_antisymm
  · exact dist_le_sqrt_of_dist_sq_le hR h.le
  · have hsq : Real.sqrt R ^ 2 ≤ dist x y ^ 2 := by rw [Real.sq_sqrt hR, h]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) dist_nonneg).mp hsq

theorem finite_diam_eq_of_forall_dist_le_of_exists_dist_eq
    {X : Type*} [PseudoMetricSpace X] (points : Finset X) {R : ℝ}
    (hR : 0 ≤ R)
    (hle : ∀ x ∈ points, ∀ y ∈ points, dist x y ≤ R)
    (hexists : ∃ x ∈ points, ∃ y ∈ points, dist x y = R) :
    Metric.diam (points : Set X) = R := by
  have hupper : Metric.diam (points : Set X) ≤ R :=
    Metric.diam_le_of_forall_dist_le hR (by simpa using hle)
  obtain ⟨x, hx, y, hy, hdist⟩ := hexists
  have hlower : R ≤ Metric.diam (points : Set X) := by
    rw [← hdist]
    exact Metric.dist_le_diam_of_mem (Finset.finite_toSet points).isBounded hx hy
  exact le_antisymm hupper hlower





theorem kahnKalai_undirected_quadratic_bound_real {p x : ℕ} (hx : x ≤ 2 * p) :
    ((2 * x * (4 * p - 2 * x) : ℕ) : ℝ) ≤ ((4 * p * p : ℕ) : ℝ) := by
  have hx2 : 2 * x ≤ 4 * p := by nlinarith
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hx2]
  norm_num
  have hs : 0 ≤ ((x : ℝ) - p) ^ 2 := sq_nonneg _
  nlinarith



































theorem eq_of_inter_card_eq_left_card_of_card_eq {α : Type*} [DecidableEq α]
    {A B : Finset α} (hinter : (A ∩ B).card = A.card) (hcard : A.card = B.card) :
    A = B := by
  have hInterA : A ∩ B = A := by
    exact Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
  have hsub : A ⊆ B := by
    intro a ha
    have : a ∈ A ∩ B := by simpa [hInterA]
    exact (Finset.mem_inter.mp this).2
  exact Finset.eq_of_subset_of_card_le hsub (by omega)











theorem dist_eq_of_dist_sq_eq_diam_sq {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {x y : X} (h : dist x y ^ 2 = Metric.diam S ^ 2) :
    dist x y = Metric.diam S := by
  have habs : |dist x y| = |Metric.diam S| :=
    (sq_eq_sq_iff_abs_eq_abs _ _).mp h
  rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg Metric.diam_nonneg] at habs

theorem diam_pos_of_diam_sq_eq_pos {X : Type*} [PseudoMetricSpace X]
    {S : Set X} {r : ℝ} (h : Metric.diam S ^ 2 = r) (hr : 0 < r) :
    0 < Metric.diam S := by
  have hne : Metric.diam S ≠ 0 := by
    intro hzero
    have hr0 : r = 0 := by simpa [hzero] using h.symm
    exact (ne_of_gt hr) hr0
  exact lt_of_le_of_ne' Metric.diam_nonneg hne

/-- Borsuk's conjecture in dimension d: every bounded set with positive
diameter can be covered by d+1 subsets of itself, each of strictly smaller
diameter.  The subset condition is essential: in a noncompact proper space
`Metric.diam Set.univ = 0`, so allowing arbitrary covering sets would make the
formal statement spuriously true. -/
def BorsukConjecture (d : ℕ) : Prop :=
  ∀ (S : Set (EuclideanSpace ℝ (Fin d))),
    Bornology.IsBounded S → 0 < Metric.diam S →
    ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
      S ⊆ ⋃ i, parts i ∧
      (∀ i, parts i ⊆ S) ∧
      ∀ i, Metric.diam (parts i) < Metric.diam S

/--
A Kahn-Kalai certificate is a counterexample set in `ℝ^d` that is bounded,
has positive diameter, but cannot be covered by `d + 1` subsets of itself with
strictly smaller diameter.
-/
structure KahnKalaiCertificate (d : ℕ) where
  S : Set (EuclideanSpace ℝ (Fin d))
  bounded : Bornology.IsBounded S
  pos_diam : 0 < Metric.diam S
  no_partition : ¬ ∃ parts : Fin (d + 1) → Set (EuclideanSpace ℝ (Fin d)),
    S ⊆ ⋃ i, parts i ∧
    (∀ i, parts i ⊆ S) ∧
    ∀ i, Metric.diam (parts i) < Metric.diam S

/--
A finite point configuration gives a Kahn-Kalai certificate once every
`(d + 1)`-coloring has a monochromatic pair at the full diameter of the
configuration.  This is the geometric interface needed after the
Frankl-Wilson set-system construction: the combinatorics only has to rule out
small-diameter color classes.
-/
def KahnKalaiCertificate.ofFiniteDiameterObstruction {d : ℕ}
    (points : Finset (EuclideanSpace ℝ (Fin d)))
    (hpos : 0 < Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))))
    (hobstruction : ∀ color : EuclideanSpace ℝ (Fin d) → Fin (d + 1),
      ∃ x ∈ points, ∃ y ∈ points,
        color x = color y ∧ dist x y = Metric.diam (points : Set (EuclideanSpace ℝ (Fin d)))) :
    KahnKalaiCertificate d := by
  classical
  refine ⟨(points : Set (EuclideanSpace ℝ (Fin d))), (Finset.finite_toSet points).isBounded,
    hpos, ?_⟩
  rintro ⟨parts, hcover, hsub, hsmall⟩
  let color : EuclideanSpace ℝ (Fin d) → Fin (d + 1) := fun x =>
    if hx : x ∈ (points : Set (EuclideanSpace ℝ (Fin d))) then
      Classical.choose (Set.mem_iUnion.mp (hcover hx))
    else 0
  have hmem_part {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ points) :
      x ∈ parts (color x) := by
    have hxset : x ∈ (points : Set (EuclideanSpace ℝ (Fin d))) := by simpa using hx
    dsimp [color]
    simpa [hxset] using Classical.choose_spec (Set.mem_iUnion.mp (hcover hxset))
  obtain ⟨x, hx, y, hy, hsame, hdiam⟩ := hobstruction color
  have hxpart : x ∈ parts (color x) := hmem_part hx
  have hypart : y ∈ parts (color x) := by
    have hy' : y ∈ parts (color y) := hmem_part hy
    simpa [hsame] using hy'
  have hpart_bounded : Bornology.IsBounded (parts (color x)) :=
    (Finset.finite_toSet points).isBounded.subset (hsub (color x))
  have hle : dist x y ≤ Metric.diam (parts (color x)) :=
    Metric.dist_le_diam_of_mem hpart_bounded hxpart hypart
  rw [hdiam] at hle
  exact not_lt_of_ge hle (hsmall (color x))

/--
Squared-distance version of `ofFiniteDiameterObstruction`.  This is convenient
for incidence-vector constructions, where the natural formulas compute
distance squared as a Hamming count.
-/
def KahnKalaiCertificate.ofFiniteSquaredDiameterObstruction {d : ℕ}
    (points : Finset (EuclideanSpace ℝ (Fin d)))
    (hpos : 0 < Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))))
    (hobstruction : ∀ color : EuclideanSpace ℝ (Fin d) → Fin (d + 1),
      ∃ x ∈ points, ∃ y ∈ points,
        color x = color y ∧
          dist x y ^ 2 = Metric.diam (points : Set (EuclideanSpace ℝ (Fin d))) ^ 2) :
    KahnKalaiCertificate d :=
  KahnKalaiCertificate.ofFiniteDiameterObstruction points hpos fun color => by
    obtain ⟨x, hx, y, hy, hsame, hsq⟩ := hobstruction color
    exact ⟨x, hx, y, hy, hsame, dist_eq_of_dist_sq_eq_diam_sq hsq⟩



















































/-- The fixed-layer type used by the `p = 13` Kahn-Kalai construction. -/
abbrev Fin51Subsets25 := FixedCardSubsets (Fin 51) 25

theorem zmod13_fixed25_coeff_nonzero (I : Finset (Fin 51)) (hI : I.card ≤ 12) :
    ((25 - I.card).choose (12 - I.card) : ZMod 13) ≠ 0 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  interval_cases h : I.card <;> decide

theorem zmod13_nat_25_eq_neg_one : ((25 : ZMod 13) = -1) := by
  trans (12 : ZMod 13)
  · change ((25 : ℕ) : ZMod 13) = ((12 : ℕ) : ZMod 13)
    rw [ZMod.natCast_eq_natCast_iff]
    norm_num [Nat.ModEq]
  · symm
    decide

theorem nat_eq_12_of_zmod13_eq_neg_one_of_le_25_of_ne_25 {n : ℕ}
    (hcast : ((n : ZMod 13) = -1)) (hle : n ≤ 25) (hne25 : n ≠ 25) :
    n = 12 := by
  interval_cases h : n <;> try omega
  all_goals
    exfalso
    revert hcast
    decide +revert

/--
Fixed-layer Frankl-Wilson, specialized to the Kahn-Kalai `p = 13` numbers.
Any coloring of the 25-subsets of a 51-set with sufficiently few colors has a
monochromatic pair with intersection exactly `12`.
-/
theorem exists_monochromatic_pair_fin51_25_intersection_12
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (color : Fin51Subsets25 → κ)
    (hlarge : Fintype.card κ * Nat.choose 51 12 < Nat.choose 51 25) :
    ∃ A B : Fin51Subsets25, A ≠ B ∧ color A = color B ∧ (A.1 ∩ B.1).card = 12 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let L : Finset (ZMod 13) := Finset.univ.erase (-1 : ZMod 13)
  have hLcard : L.card = 12 := by
    simp [L, ZMod.card]
  have hcard : ∀ A : Fin51Subsets25, A.1.card = 25 := fun A => A.2
  have hself : ∀ A : Fin51Subsets25, ((A.1.card : ZMod 13) ∉ L) := by
    intro A
    rw [A.2]
    simpa [L] using zmod13_nat_25_eq_neg_one
  have hlarge' :
      Fintype.card κ * Fintype.card {I : Finset (Fin 51) // I.card = L.card} <
        Fintype.card Fin51Subsets25 := by
    rw [exactSubsets_card_eq_choose, hLcard]
    change Fintype.card κ * Nat.choose (Fintype.card (Fin 51)) 12 <
      Fintype.card (FixedCardSubsets (Fin 51) 25)
    rw [Fintype.card_fin]
    rw [show Fintype.card (FixedCardSubsets (Fin 51) 25) = Nat.choose 51 25 by
      rw [exactSubsets_card_eq_choose, Fintype.card_fin]]
    exact hlarge
  obtain ⟨A, B, hne, hsame, hnot⟩ :=
    exists_monochromatic_pair_fixed_card_intersection_notMem
      (K := ZMod 13) (α := Fin 51) (ι := Fin51Subsets25) (κ := κ)
      (q := 25) (sets := fun A => A.1) (L := L) color hcard
      (by
        intro I hI
        rw [hLcard]
        exact zmod13_fixed25_coeff_nonzero I hI)
      hself hlarge'
  have hcast : (((A.1 ∩ B.1).card : ZMod 13) = -1) := by
    have hne_minus : (((A.1 ∩ B.1).card : ZMod 13) ≠ -1) → False := by
      intro hne'
      exact hnot (by simp [L, hne'])
    exact Classical.byContradiction hne_minus
  have hle : (A.1 ∩ B.1).card ≤ 25 := by
    have := Finset.card_le_card (Finset.inter_subset_left (s₁ := A.1) (s₂ := B.1))
    omega
  have hne25 : (A.1 ∩ B.1).card ≠ 25 := by
    intro h25
    have hAeqB : A.1 = B.1 := by
      exact eq_of_inter_card_eq_left_card_of_card_eq (by simpa [A.2] using h25)
        (by rw [A.2, B.2])
    exact hne (Subtype.ext hAeqB)
  exact ⟨A, B, hne, hsame,
    nat_eq_12_of_zmod13_eq_neg_one_of_le_25_of_ne_25 hcast hle hne25⟩

noncomputable def fin52SetOfErased (A : Fin51Subsets25) : Finset (Fin 52) :=
  insert 0 (A.1.image (Fin.succEmb 51))

theorem fin52SetOfErased_card (A : Fin51Subsets25) :
    (fin52SetOfErased A).card = 26 := by
  rw [fin52SetOfErased, Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (Fin.succEmb 51).injective, A.2]
  · intro h
    rcases Finset.mem_image.mp h with ⟨a, _ha, h0⟩
    exact Fin.succ_ne_zero a h0

theorem fin52SetOfErased_inter (A B : Fin51Subsets25) :
    fin52SetOfErased A ∩ fin52SetOfErased B =
      insert 0 ((A.1 ∩ B.1).image (Fin.succEmb 51)) := by
  ext x
  by_cases hx0 : x = 0
  · subst x
    simp [fin52SetOfErased]
  · simp [fin52SetOfErased, hx0, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, rfl⟩, b, hb, hs⟩
      have hab : a = b := (Fin.succEmb 51).injective hs.symm
      subst b
      exact ⟨a, ⟨ha, hb⟩, rfl⟩
    · rintro ⟨a, ⟨ha, hb⟩, rfl⟩
      exact ⟨⟨a, ha, rfl⟩, ⟨a, hb, rfl⟩⟩

theorem fin52SetOfErased_inter_card (A B : Fin51Subsets25) :
    (fin52SetOfErased A ∩ fin52SetOfErased B).card = (A.1 ∩ B.1).card + 1 := by
  rw [fin52SetOfErased_inter]
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_image_of_injective _ (Fin.succEmb 51).injective]
  · intro h
    rcases Finset.mem_image.mp h with ⟨a, _ha, h0⟩
    exact Fin.succ_ne_zero a h0

theorem fin52SetOfErased_inter_card_of_erased_eq_12 {A B : Fin51Subsets25}
    (h : (A.1 ∩ B.1).card = 12) :
    (fin52SetOfErased A ∩ fin52SetOfErased B).card = 13 := by
  rw [fin52SetOfErased_inter_card, h]

theorem undirectedEdge_fin52_card : Fintype.card (UndirectedEdge (Fin 52)) = 1326 := by
  rw [Sym2.card_subtype_not_diag, Fintype.card_fin]
  norm_num [Nat.choose_succ_succ]

theorem fixed25_numeric_large_1326 :
    (1326 + 1) * Nat.choose 51 12 < Nat.choose 51 25 := by
  norm_num [Nat.choose_succ_succ]

theorem fixed25_numeric_large_1325 :
    (1325 + 1) * Nat.choose 51 12 < Nat.choose 51 25 := by
  norm_num [Nat.choose_succ_succ]



noncomputable def sumCoordinatesLinear (β : Type*) [Fintype β] :
    EuclideanSpace ℝ β →ₗ[ℝ] ℝ where
  toFun v := ∑ b, v b
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.mul_sum]

noncomputable abbrev zeroSumEuclideanSubmodule (β : Type*) [Fintype β] :
    Submodule ℝ (EuclideanSpace ℝ β) :=
  LinearMap.ker (sumCoordinatesLinear β)

theorem sumCoordinatesLinear_ne_zero {β : Type*} [Fintype β] [Nonempty β] :
    sumCoordinatesLinear β ≠ 0 := by
  intro hzero
  let v : EuclideanSpace ℝ β := WithLp.toLp 2 fun _ => (1 : ℝ)
  have hv := congrArg (fun f : EuclideanSpace ℝ β →ₗ[ℝ] ℝ => f v) hzero
  simp [sumCoordinatesLinear, v] at hv

theorem sumCoordinatesLinear_realIncidencePoint {β : Type*} [Fintype β] [DecidableEq β]
    (A : Finset β) :
    sumCoordinatesLinear β (realIncidencePoint A) = (A.card : ℝ) := by
  rw [Finset.card_eq_sum_ones]
  simp [sumCoordinatesLinear, realIncidencePoint]

theorem sumCoordinatesLinear_sub_realIncidencePoint {β : Type*} [Fintype β]
    [DecidableEq β] (A B : Finset β) :
    sumCoordinatesLinear β (realIncidencePoint A - realIncidencePoint B) =
      (A.card : ℝ) - (B.card : ℝ) := by
  rw [map_sub, sumCoordinatesLinear_realIncidencePoint, sumCoordinatesLinear_realIncidencePoint]

noncomputable def centeredIncidencePoint {β : Type*} [Fintype β] [DecidableEq β]
    (A0 A : Finset β) (hcard : A.card = A0.card) : zeroSumEuclideanSubmodule β := by
  refine ⟨realIncidencePoint A - realIncidencePoint A0, ?_⟩
  rw [LinearMap.mem_ker, sumCoordinatesLinear_sub_realIncidencePoint]
  norm_num [hcard]

theorem centeredIncidencePoint_dist_sq {β : Type*} [Fintype β] [DecidableEq β]
    (A0 A B : Finset β) (hA : A.card = A0.card) (hB : B.card = A0.card) :
    dist (centeredIncidencePoint A0 A hA) (centeredIncidencePoint A0 B hB) ^ 2 =
      (finsetSymmDiffCard A B : ℝ) := by
  rw [dist_eq_norm]
  change ‖(realIncidencePoint A - realIncidencePoint A0) -
      (realIncidencePoint B - realIncidencePoint A0)‖ ^ 2 = (finsetSymmDiffCard A B : ℝ)
  rw [sub_sub_sub_cancel_right]
  rw [← dist_eq_norm, realIncidencePoint_dist_sq]

theorem undirectedEdge_fin52_nonempty : Nonempty (UndirectedEdge (Fin 52)) := by
  refine ⟨⟨s((0 : Fin 52), (1 : Fin 52)), ?_⟩⟩
  rw [Sym2.mk_isDiag_iff]
  norm_num

theorem zeroSumUndirected52_finrank :
    Module.finrank ℝ (zeroSumEuclideanSubmodule (UndirectedEdge (Fin 52))) = 1325 := by
  haveI : Nonempty (UndirectedEdge (Fin 52)) := undirectedEdge_fin52_nonempty
  have hker := Module.Dual.finrank_ker_add_one_of_ne_zero
    (f := sumCoordinatesLinear (UndirectedEdge (Fin 52)))
    (sumCoordinatesLinear_ne_zero (β := UndirectedEdge (Fin 52)))
  change Module.finrank ℝ (zeroSumEuclideanSubmodule (UndirectedEdge (Fin 52))) + 1 =
      Module.finrank ℝ (EuclideanSpace ℝ (UndirectedEdge (Fin 52))) at hker
  rw [finrank_euclideanSpace, undirectedEdge_fin52_card] at hker
  omega

noncomputable def zeroSumUndirected52Basis :
    OrthonormalBasis (Fin 1325) ℝ (zeroSumEuclideanSubmodule (UndirectedEdge (Fin 52))) :=
  (stdOrthonormalBasis ℝ (zeroSumEuclideanSubmodule (UndirectedEdge (Fin 52)))).reindex
    (finCongr zeroSumUndirected52_finrank)

noncomputable def fin51Subsets25Base : Fin51Subsets25 := by
  classical
  refine Classical.choice ?_
  rw [← Fintype.card_pos_iff]
  rw [exactSubsets_card_eq_choose, Fintype.card_fin]
  norm_num [Nat.choose_succ_succ]

/--
The codimension-one Kahn-Kalai cut realization.  Incidence vectors of the
unordered cuts all have the same coordinate sum, so translating by one fixed cut
puts them in the zero-sum subspace of `ℝ^1326`, whose finrank is `1325`.
-/
noncomputable def centeredUndirectedCutPoint1325 (A : Fin51Subsets25) :
    EuclideanSpace ℝ (Fin 1325) :=
  zeroSumUndirected52Basis.repr
    (centeredIncidencePoint (undirectedCutSet (fin52SetOfErased fin51Subsets25Base))
      (undirectedCutSet (fin52SetOfErased A)) (by
        rw [undirectedCutSet_card, undirectedCutSet_card, fin52SetOfErased_card A,
          fin52SetOfErased_card fin51Subsets25Base]))

theorem centeredUndirectedCutPoint1325_dist_sq (A B : Fin51Subsets25) :
    dist (centeredUndirectedCutPoint1325 A) (centeredUndirectedCutPoint1325 B) ^ 2 =
      (finsetSymmDiffCard (undirectedCutSet (fin52SetOfErased A))
        (undirectedCutSet (fin52SetOfErased B)) : ℝ) := by
  unfold centeredUndirectedCutPoint1325
  rw [Isometry.dist_eq zeroSumUndirected52Basis.repr.isometry]
  exact centeredIncidencePoint_dist_sq _ _ _ _ _

theorem centeredUndirectedCutPoint1325_dist_sq_of_intersection
    {A B : Fin51Subsets25} (hinter : (fin52SetOfErased A ∩ fin52SetOfErased B).card = 13) :
    dist (centeredUndirectedCutPoint1325 A) (centeredUndirectedCutPoint1325 B) ^ 2 =
      ((4 * 13 * 13 : ℕ) : ℝ) := by
  rw [centeredUndirectedCutPoint1325_dist_sq]
  rw [undirectedCutSet_symmDiffCard_of_kahnKalai_intersection (fin52SetOfErased A)
    (fin52SetOfErased B) (by norm_num : Fintype.card (Fin 52) = 4 * 13)
    (fin52SetOfErased_card A) (fin52SetOfErased_card B) hinter]

theorem centeredUndirectedCutPoint1325_dist_sq_le (A B : Fin51Subsets25) :
    dist (centeredUndirectedCutPoint1325 A) (centeredUndirectedCutPoint1325 B) ^ 2 ≤
      ((4 * 13 * 13 : ℕ) : ℝ) := by
  rw [centeredUndirectedCutPoint1325_dist_sq]
  rw [undirectedCutSet_symmDiffCard_of_card_eq (fin52SetOfErased A) (fin52SetOfErased B)
    (fin52SetOfErased_card A) (fin52SetOfErased_card B),
    show Fintype.card (Fin 52) = 4 * 13 by norm_num]
  exact kahnKalai_undirected_quadratic_bound_real (p := 13) (Nat.sub_le _ _)

theorem centeredUndirectedCutPoint1325_dist_le (A B : Fin51Subsets25) :
    dist (centeredUndirectedCutPoint1325 A) (centeredUndirectedCutPoint1325 B) ≤
      Real.sqrt ((4 * 13 * 13 : ℕ) : ℝ) :=
  dist_le_sqrt_of_dist_sq_le (Nat.cast_nonneg _)
    (centeredUndirectedCutPoint1325_dist_sq_le A B)

theorem centeredUndirectedCutFamily1325_diam_sq_eq
    (hexists : ∃ A B : Fin51Subsets25, (fin52SetOfErased A ∩ fin52SetOfErased B).card = 13) :
    Metric.diam
      ((Finset.univ.image centeredUndirectedCutPoint1325 :
          Finset (EuclideanSpace ℝ (Fin 1325))) : Set (EuclideanSpace ℝ (Fin 1325))) ^ 2 =
        ((4 * 13 * 13 : ℕ) : ℝ) := by
  have hdiam_eq : Metric.diam
      ((Finset.univ.image centeredUndirectedCutPoint1325 :
          Finset (EuclideanSpace ℝ (Fin 1325))) : Set (EuclideanSpace ℝ (Fin 1325))) =
      Real.sqrt ((4 * 13 * 13 : ℕ) : ℝ) := by
    let points : Finset (EuclideanSpace ℝ (Fin 1325)) :=
      Finset.univ.image centeredUndirectedCutPoint1325
    refine finite_diam_eq_of_forall_dist_le_of_exists_dist_eq points (Real.sqrt_nonneg _) ?_ ?_
    · intro x hx y hy
      rcases Finset.mem_image.mp hx with ⟨A, _hA, rfl⟩
      rcases Finset.mem_image.mp hy with ⟨B, _hB, rfl⟩
      exact centeredUndirectedCutPoint1325_dist_le A B
    · obtain ⟨A, B, hinter⟩ := hexists
      refine ⟨centeredUndirectedCutPoint1325 A, ?_, centeredUndirectedCutPoint1325 B, ?_, ?_⟩
      · simp [points]
      · simp [points]
      · exact dist_eq_sqrt_of_dist_sq_eq (Nat.cast_nonneg _)
          (centeredUndirectedCutPoint1325_dist_sq_of_intersection hinter)
  rw [hdiam_eq, Real.sq_sqrt]
  exact Nat.cast_nonneg _

/-- A fully constructed Kahn-Kalai certificate in the book's dimension `1325`. -/
noncomputable def kahnKalaiCertificate_1325 : KahnKalaiCertificate 1325 := by
  classical
  let pointOf : Fin51Subsets25 → EuclideanSpace ℝ (Fin 1325) :=
    centeredUndirectedCutPoint1325
  have hlarge_colors :
      Fintype.card (Fin (1325 + 1)) * Nat.choose 51 12 < Nat.choose 51 25 := by
    simpa [Fintype.card_fin] using fixed25_numeric_large_1325
  have hlarge_unit : Fintype.card Unit * Nat.choose 51 12 < Nat.choose 51 25 := by
    have hle : Nat.choose 51 12 ≤ (1325 + 1) * Nat.choose 51 12 := by
      exact Nat.le_mul_of_pos_left _ (by norm_num : 0 < 1325 + 1)
    simpa using lt_of_le_of_lt hle fixed25_numeric_large_1325
  have hexists : ∃ A B : Fin51Subsets25, (fin52SetOfErased A ∩ fin52SetOfErased B).card = 13 := by
    obtain ⟨A0, B0, _hne0, _hsame0, hinter0_erased⟩ :=
      exists_monochromatic_pair_fin51_25_intersection_12 (κ := Unit) (fun _ => ())
        hlarge_unit
    exact ⟨A0, B0, fin52SetOfErased_inter_card_of_erased_eq_12 hinter0_erased⟩
  have hdiamSq : Metric.diam
      ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin 1325))) :
        Set (EuclideanSpace ℝ (Fin 1325))) ^ 2 = ((4 * 13 * 13 : ℕ) : ℝ) := by
    simpa [pointOf] using centeredUndirectedCutFamily1325_diam_sq_eq hexists
  have hpos : 0 < Metric.diam
      ((Finset.univ.image pointOf : Finset (EuclideanSpace ℝ (Fin 1325))) :
        Set (EuclideanSpace ℝ (Fin 1325))) := by
    have hsq_pos : (0 : ℝ) < ((4 * 13 * 13 : ℕ) : ℝ) := by norm_num
    exact diam_pos_of_diam_sq_eq_pos hdiamSq hsq_pos
  refine KahnKalaiCertificate.ofFiniteSquaredDiameterObstruction
    (Finset.univ.image pointOf) hpos ?_
  intro color
  obtain ⟨A, B, _hne, hsame, hinter_erased⟩ :=
    exists_monochromatic_pair_fin51_25_intersection_12
      (κ := Fin (1325 + 1)) (fun A => color (pointOf A)) hlarge_colors
  refine ⟨pointOf A, ?_, pointOf B, ?_, hsame, ?_⟩
  · simp [pointOf]
  · simp [pointOf]
  · have hinter : (fin52SetOfErased A ∩ fin52SetOfErased B).card = 13 :=
      fin52SetOfErased_inter_card_of_erased_eq_12 hinter_erased
    rw [centeredUndirectedCutPoint1325_dist_sq_of_intersection hinter, hdiamSq]









































end ProofsInTheBook.Chapter16


