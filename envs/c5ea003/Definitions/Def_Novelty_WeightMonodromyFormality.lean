-- Prove2me | Definitions.Def_Novelty_WeightMonodromyFormality
-- name    : Novelty_WeightMonodromyFormality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:50:52.441241+00:00
-- url     : https://prove2.me/theorems/99d4eddc-45ae-477c-9f41-a3703beab2cf
-- title:
--   Aether Catalog definitions — Novelty_WeightMonodromyFormality
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.WeightMonodromyFormality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/WeightMonodromyFormality.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Formality of weight-graded dg-algebras (algebraic core of weight-monodromy formality)

This file formalises the algebraic mechanism behind the theorem that the étale and de Rham
cohomology algebras of a smooth proper rigid-analytic space over a finite extension of `Q_p`
are *formal* as soon as the space satisfies the weight-monodromy conjecture.

The geometric input (rigid-analytic spaces, comparison theorems, the monodromy filtration) is
not formalised here.  What *is* formalised is the purely algebraic statement that carries the
whole argument:

> A differential graded algebra equipped with an additional *weight* grading, whose cohomology
> is **pure** (the weight of a class of cohomological degree `n` equals `n`), is formal.

Weight-monodromy is exactly what guarantees purity of the weight grading in the rigid-analytic
setting; formality is then a formal consequence of purity, which is what we prove.

## Main definitions

* `WeightedDGA 𝒜` : a differential graded algebra structure on a bigraded algebra
  `𝒜 : ℤ × ℤ → Submodule k A` (first index = cohomological degree, second index = weight).
* `IsWeightPure 𝒜 D` : purity, i.e. every cocycle of bidegree `(n, w)` with `w ≠ n` is a
  coboundary of an element of the *same* weight.
* `subDGA`, `idealDGA` : the sub-dg-algebra `A'` obtained by weight-wise canonical truncation,
  and the acyclic ideal `J ⊆ A'` whose quotient is the cohomology algebra.
* `StrictFormalityData` : a strict formality zig-zag `A ⊇ A' ↠ A'/J` in which the quotient
  carries the zero differential.

## Main results

* `formality_of_weight_purity` : purity implies formality, producing an explicit
  `StrictFormalityData`.
* `StrictFormalityData.cohomology_surj` / `StrictFormalityData.exact_iff_mem_ideal` :
  the quotient `A'/J` really is the cohomology algebra of `A`.

The Massey product consequences (and the resulting obstruction to weight-monodromy for
non-formal spaces) are in `Catalog/Novelty/WeightMonodromyMassey.lean`.
-/

namespace WeightMonodromy

open scoped Classical

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]

section Components

variable (𝒜 : ℤ × ℤ → Submodule k A) [GradedAlgebra 𝒜]

/-- The `i`-th bihomogeneous component of an element, as a `k`-linear map. -/
noncomputable def cmpL (i : ℤ × ℤ) : A →ₗ[k] A :=
  (𝒜 i).subtype ∘ₗ (DFinsupp.lapply i) ∘ₗ (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

lemma cmpL_mem (a : A) (i : ℤ × ℤ) : cmpL 𝒜 i a ∈ 𝒜 i := (DirectSum.decompose 𝒜 a i).2

lemma cmpL_of_mem_ne {a : A} {i j : ℤ × ℤ} (h : a ∈ 𝒜 i) (hij : i ≠ j) : cmpL 𝒜 j a = 0 :=
  DirectSum.decompose_of_mem_ne 𝒜 h hij

lemma cmpL_of_mem_same {a : A} {i : ℤ × ℤ} (h : a ∈ 𝒜 i) : cmpL 𝒜 i a = a :=
  DirectSum.decompose_of_mem_same 𝒜 h

/-- The (finite) support of the bihomogeneous decomposition of `a`. -/
noncomputable def supp (a : A) : Finset (ℤ × ℤ) := (DirectSum.decompose 𝒜 a).support

lemma sum_cmpL (a : A) : ∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a = a :=
  DirectSum.sum_support_decompose 𝒜 a

lemma cmpL_zero_of_notMem_supp {a : A} {i : ℤ × ℤ} (h : i ∉ supp 𝒜 a) : cmpL 𝒜 i a = 0 := by
  have h2 := DFinsupp.notMem_support_iff.mp h
  show ((DirectSum.decompose 𝒜 a i : 𝒜 i) : A) = 0
  rw [h2]; rfl

end Components

/-- A differential graded algebra structure on a bigraded `k`-algebra `𝒜`, where the first
index is the cohomological degree and the second index is the weight.  The differential raises
the degree by one and preserves the weight; the Leibniz rule uses an arbitrary nowhere-zero
sign function `sgn` (in the classical case `sgn n = (-1)^n`). -/
structure WeightedDGA (𝒜 : ℤ × ℤ → Submodule k A) [GradedAlgebra 𝒜] where
  /-- The differential. -/
  d : A →ₗ[k] A
  /-- The Koszul sign function. -/
  sgn : ℤ → k
  sgn_ne_zero : ∀ n, sgn n ≠ 0
  d_mem : ∀ (i : ℤ × ℤ) (a : A), a ∈ 𝒜 i → d a ∈ 𝒜 (i.1 + 1, i.2)
  d_comp_d : ∀ a, d (d a) = 0
  leibniz : ∀ (n w : ℤ) (a b : A), a ∈ 𝒜 (n, w) → d (a * b) = d a * b + sgn n • (a * d b)

variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Purity of the weight grading on cohomology: in bidegree `(n, w)` with `w ≠ n` there is no
cohomology, and moreover the primitive can be chosen of the same weight.  This is what the
weight-monodromy conjecture provides in the rigid-analytic setting. -/
def IsWeightPure (D : WeightedDGA 𝒜) : Prop :=
  ∀ n w : ℤ, n ≠ w → ∀ a ∈ 𝒜 (n, w), D.d a = 0 → ∃ c ∈ 𝒜 (n - 1, w), D.d c = a

namespace WeightedDGA

variable (D : WeightedDGA 𝒜)

lemma cmpL_d (a : A) (n w : ℤ) : cmpL 𝒜 (n + 1, w) (D.d a) = D.d (cmpL 𝒜 (n, w) a) := by
  have ha : a = ∑ i ∈ supp 𝒜 a, cmpL 𝒜 i a := (sum_cmpL 𝒜 a).symm
  have h1 : cmpL 𝒜 (n + 1, w) (D.d a)
      = ∑ i ∈ supp 𝒜 a, cmpL 𝒜 (n + 1, w) (D.d (cmpL 𝒜 i a)) := by
    conv_lhs => rw [ha]
    simp [map_sum]
  rw [h1, Finset.sum_eq_single (n, w)]
  · exact cmpL_of_mem_same 𝒜 (D.d_mem (n, w) _ (cmpL_mem 𝒜 a (n, w)))
  · intro i _ hi
    have hm : D.d (cmpL 𝒜 i a) ∈ 𝒜 (i.1 + 1, i.2) := D.d_mem i _ (cmpL_mem 𝒜 a i)
    refine cmpL_of_mem_ne 𝒜 hm ?_
    intro hcon
    simp only [Prod.mk.injEq] at hcon
    exact hi (Prod.ext (by omega) hcon.2)
  · intro hns
    rw [cmpL_zero_of_notMem_supp 𝒜 hns]
    simp

/-- Components of a cocycle are cocycles. -/
lemma cmpL_cocycle {a : A} (ha : D.d a = 0) (i : ℤ × ℤ) : D.d (cmpL 𝒜 i a) = 0 := by
  have h := D.cmpL_d a i.1 i.2
  simp only [Prod.mk.eta] at h
  rw [← h, ha, map_zero]

lemma d_one : D.d 1 = 0 := by
  have h1 : (1 : A) ∈ 𝒜 (0, 0) := by
    have := SetLike.one_mem_graded 𝒜
    simpa using this
  have := D.leibniz 0 0 1 1 h1
  simp only [one_mul, mul_one] at this
  have h2 : D.d 1 = D.d 1 + D.sgn 0 • D.d 1 := this
  have h3 : D.sgn 0 • D.d 1 = 0 := by
    have := congrArg (fun x => x - D.d 1) h2
    simpa using this.symm
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h (D.sgn_ne_zero 0)
  · exact h

end WeightedDGA

section Construction

variable (D : WeightedDGA 𝒜)

/-- The bihomogeneous pieces of the sub-dg-algebra `A'`: everything below the diagonal
`degree = weight`, the cocycles on the diagonal, and nothing above it. -/
noncomputable def pieceSub (i : ℤ × ℤ) : Submodule k A :=
  if i.1 < i.2 then 𝒜 i else if i.1 = i.2 then 𝒜 i ⊓ LinearMap.ker D.d else ⊥

/-- The bihomogeneous pieces of the acyclic ideal `J`: everything below the diagonal, and the
coboundaries on the diagonal. -/
noncomputable def pieceIdeal (i : ℤ × ℤ) : Submodule k A :=
  if i.1 < i.2 then 𝒜 i else if i.1 = i.2 then (𝒜 (i.1 - 1, i.2)).map D.d else ⊥

/-- The weight-wise canonical truncation of `A`: a sub-dg-algebra quasi-isomorphic to `A`. -/
noncomputable def subDGA : Submodule k A := ⨆ i, pieceSub D i

/-- The acyclic ideal of `subDGA` whose quotient is the cohomology algebra. -/
noncomputable def idealDGA : Submodule k A := ⨆ i, pieceIdeal D i

lemma pieceSub_le_graded (i : ℤ × ℤ) : pieceSub D i ≤ 𝒜 i := by
  unfold pieceSub
  split_ifs with h1 h2
  · exact le_rfl
  · exact inf_le_left
  · exact bot_le

lemma pieceIdeal_le_pieceSub (i : ℤ × ℤ) : pieceIdeal D i ≤ pieceSub D i := by
  unfold pieceIdeal pieceSub
  split_ifs with h1 h2
  · exact le_rfl
  · rintro x ⟨c, hc, rfl⟩
    refine ⟨?_, ?_⟩
    · have hm := D.d_mem (i.1 - 1, i.2) c hc
      simpa [show i.1 - 1 + 1 = i.1 from by omega, Prod.mk.eta] using hm
    · simp [LinearMap.mem_ker, D.d_comp_d]
  · exact bot_le

lemma idealDGA_le_subDGA : idealDGA D ≤ subDGA D :=
  iSup_mono fun i => pieceIdeal_le_pieceSub D i

lemma pieceSub_eq_bot {i : ℤ × ℤ} (h : i.2 < i.1) : pieceSub D i = ⊥ := by
  have h1 : ¬ i.1 < i.2 := by omega
  have h2 : ¬ i.1 = i.2 := by omega
  simp [pieceSub, h1, h2]

lemma pieceIdeal_eq_bot {i : ℤ × ℤ} (h : i.2 < i.1) : pieceIdeal D i = ⊥ := by
  have h1 : ¬ i.1 < i.2 := by omega
  have h2 : ¬ i.1 = i.2 := by omega
  simp [pieceIdeal, h1, h2]

lemma mem_subDGA_of_lt {i : ℤ × ℤ} (h : i.1 < i.2) {a : A} (ha : a ∈ 𝒜 i) : a ∈ subDGA D := by
  refine le_iSup (pieceSub D) i ?_
  simpa [pieceSub, h] using ha

lemma mem_subDGA_of_diag {i : ℤ × ℤ} (h : i.1 = i.2) {a : A} (ha : a ∈ 𝒜 i)
    (hd : D.d a = 0) : a ∈ subDGA D := by
  refine le_iSup (pieceSub D) i ?_
  have : ¬ i.1 < i.2 := by omega
  simp only [pieceSub, if_neg this, if_pos h]
  exact ⟨ha, by simpa using hd⟩

lemma mem_idealDGA_of_lt {i : ℤ × ℤ} (h : i.1 < i.2) {a : A} (ha : a ∈ 𝒜 i) :
    a ∈ idealDGA D := by
  refine le_iSup (pieceIdeal D) i ?_
  simpa [pieceIdeal, h] using ha

lemma mem_idealDGA_of_diag {i : ℤ × ℤ} (h : i.1 = i.2) {c : A} (hc : c ∈ 𝒜 (i.1 - 1, i.2)) :
    D.d c ∈ idealDGA D := by
  refine le_iSup (pieceIdeal D) i ?_
  have : ¬ i.1 < i.2 := by omega
  simp only [pieceIdeal, if_neg this, if_pos h]
  exact ⟨c, hc, rfl⟩

/-- Homogeneous multiplicativity: the pieces of `A'` multiply into `A'`. -/
lemma pieceSub_mul_le (i j : ℤ × ℤ) : pieceSub D i * pieceSub D j ≤ subDGA D := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 i := pieceSub_le_graded D i ha
  have hgj : b ∈ 𝒜 j := pieceSub_le_graded D j hb
  have hab : a * b ∈ 𝒜 (i + j) := SetLike.mul_mem_graded hgi hgj
  rcases lt_trichotomy i.1 i.2 with h1 | h1 | h1
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_subDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · exact mem_subDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · rw [pieceSub_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_subDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · -- both on the diagonal: product of cocycles is a cocycle
      have hda : D.d a = 0 := by
        have : ¬ i.1 < i.2 := by omega
        simp only [pieceSub, if_neg this, if_pos h1] at ha
        simpa using ha.2
      have hdb : D.d b = 0 := by
        have : ¬ j.1 < j.2 := by omega
        simp only [pieceSub, if_neg this, if_pos h2] at hb
        simpa using hb.2
      refine mem_subDGA_of_diag D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab ?_
      rw [D.leibniz i.1 i.2 a b (by simpa using hgi), hda, hdb]
      simp
    · rw [pieceSub_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rw [pieceSub_eq_bot D h1] at ha; simp at ha; simp [ha]

lemma subDGA_mul_mem {a b : A} (ha : a ∈ subDGA D) (hb : b ∈ subDGA D) :
    a * b ∈ subDGA D := by
  have hle : subDGA D * subDGA D ≤ subDGA D := by
    unfold subDGA
    rw [Submodule.iSup_mul]
    refine iSup_le fun i => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun j => pieceSub_mul_le D i j
  exact hle (Submodule.mul_mem_mul ha hb)

lemma one_mem_subDGA : (1 : A) ∈ subDGA D := by
  have h1 : (1 : A) ∈ 𝒜 ((0 : ℤ), (0 : ℤ)) := by simpa using SetLike.one_mem_graded 𝒜
  exact mem_subDGA_of_diag D rfl h1 D.d_one

/-- `J` absorbs multiplication by `A'` on the right. -/
lemma pieceIdeal_mul_le (i j : ℤ × ℤ) : pieceIdeal D i * pieceSub D j ≤ idealDGA D := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 i := (pieceIdeal_le_pieceSub D i).trans (pieceSub_le_graded D i) ha
  have hgj : b ∈ 𝒜 j := pieceSub_le_graded D j hb
  have hab : a * b ∈ 𝒜 (i + j) := SetLike.mul_mem_graded hgi hgj
  rcases lt_trichotomy i.1 i.2 with h1 | h1 | h1
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · rw [pieceSub_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · -- `a = d c` with `c` of weight `i.2`, and `b` a cocycle: `a * b = d (c * b)`
      obtain ⟨c, hc, rfl⟩ : ∃ c ∈ 𝒜 (i.1 - 1, i.2), D.d c = a := by
        have : ¬ i.1 < i.2 := by omega
        simp only [pieceIdeal, if_neg this, if_pos h1] at ha
        obtain ⟨c, hc, hcc⟩ := ha
        exact ⟨c, hc, hcc⟩
      have hdb : D.d b = 0 := by
        have : ¬ j.1 < j.2 := by omega
        simp only [pieceSub, if_neg this, if_pos h2] at hb
        simpa using hb.2
      have hcb : c * b ∈ 𝒜 ((i + j).1 - 1, (i + j).2) := by
        have := SetLike.mul_mem_graded hc hgj
        have he : (i.1 - 1, i.2) + j = ((i + j).1 - 1, (i + j).2) := by
          refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add]
          omega
        rwa [he] at this
      have hkey : D.d c * b = D.d (c * b) := by
        rw [D.leibniz (i.1 - 1) i.2 c b hc, hdb]
        simp
      rw [hkey]
      exact mem_idealDGA_of_diag D (by simp [Prod.fst_add, Prod.snd_add]; omega) hcb
    · rw [pieceSub_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rw [pieceIdeal_eq_bot D h1] at ha; simp at ha; simp [ha]

/-- `J` absorbs multiplication by `A'` on the left. -/
lemma mul_pieceIdeal_le (i j : ℤ × ℤ) : pieceSub D i * pieceIdeal D j ≤ idealDGA D := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 i := pieceSub_le_graded D i ha
  have hgj : b ∈ 𝒜 j := (pieceIdeal_le_pieceSub D j).trans (pieceSub_le_graded D j) hb
  have hab : a * b ∈ 𝒜 (i + j) := SetLike.mul_mem_graded hgi hgj
  rcases lt_trichotomy i.1 i.2 with h1 | h1 | h1
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · rw [pieceIdeal_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy j.1 j.2 with h2 | h2 | h2
    · exact mem_idealDGA_of_lt D (by simp [Prod.fst_add, Prod.snd_add]; omega) hab
    · obtain ⟨c, hc, rfl⟩ : ∃ c ∈ 𝒜 (j.1 - 1, j.2), D.d c = b := by
        have : ¬ j.1 < j.2 := by omega
        simp only [pieceIdeal, if_neg this, if_pos h2] at hb
        obtain ⟨c, hc, hcc⟩ := hb
        exact ⟨c, hc, hcc⟩
      have hda : D.d a = 0 := by
        have : ¬ i.1 < i.2 := by omega
        simp only [pieceSub, if_neg this, if_pos h1] at ha
        simpa using ha.2
      have hac : a * c ∈ 𝒜 ((i + j).1 - 1, (i + j).2) := by
        have := SetLike.mul_mem_graded hgi hc
        have he : i + (j.1 - 1, j.2) = ((i + j).1 - 1, (i + j).2) := by
          refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add]
          omega
        rwa [he] at this
      have hkey : a * D.d c = (D.sgn i.1)⁻¹ • D.d (a * c) := by
        rw [D.leibniz i.1 i.2 a c (by simpa using hgi), hda]
        rw [zero_mul, zero_add, smul_smul, inv_mul_cancel₀ (D.sgn_ne_zero i.1), one_smul]
      rw [hkey]
      exact Submodule.smul_mem _ _
        (mem_idealDGA_of_diag D (by simp [Prod.fst_add, Prod.snd_add]; omega) hac)
    · rw [pieceIdeal_eq_bot D h2] at hb; simp at hb; simp [hb]
  · rw [pieceSub_eq_bot D h1] at ha; simp at ha; simp [ha]

lemma idealDGA_mul_mem {a b : A} (ha : a ∈ idealDGA D) (hb : b ∈ subDGA D) :
    a * b ∈ idealDGA D := by
  have hle : idealDGA D * subDGA D ≤ idealDGA D := by
    unfold idealDGA subDGA
    rw [Submodule.iSup_mul]
    refine iSup_le fun i => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun j => pieceIdeal_mul_le D i j
  exact hle (Submodule.mul_mem_mul ha hb)

lemma mul_idealDGA_mem {a b : A} (ha : a ∈ subDGA D) (hb : b ∈ idealDGA D) :
    a * b ∈ idealDGA D := by
  have hle : subDGA D * idealDGA D ≤ idealDGA D := by
    unfold idealDGA subDGA
    rw [Submodule.iSup_mul]
    refine iSup_le fun i => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun j => mul_pieceIdeal_le D i j
  exact hle (Submodule.mul_mem_mul ha hb)

/-- The differential maps `A'` into `J`: the quotient `A'/J` carries the zero differential. -/
lemma d_subDGA_le_idealDGA : Submodule.map D.d (subDGA D) ≤ idealDGA D := by
  unfold subDGA
  rw [Submodule.map_iSup]
  refine iSup_le fun i => ?_
  rintro x ⟨a, ha, rfl⟩
  rcases lt_trichotomy i.1 i.2 with h1 | h1 | h1
  · have hga : a ∈ 𝒜 i := by simpa [pieceSub, h1] using ha
    have hda : D.d a ∈ 𝒜 (i.1 + 1, i.2) := D.d_mem i a hga
    rcases lt_or_eq_of_le (by omega : i.1 + 1 ≤ i.2) with h2 | h2
    · exact mem_idealDGA_of_lt D (by simpa using h2) hda
    · exact mem_idealDGA_of_diag D (i := (i.1 + 1, i.2)) (by simpa using h2)
        (by simpa [show i.1 + 1 - 1 = i.1 from by omega] using hga)
  · have : D.d a = 0 := by
      have hne : ¬ i.1 < i.2 := by omega
      simp only [pieceSub, if_neg hne, if_pos h1] at ha
      simpa using ha.2
    simp [this]
  · rw [pieceSub_eq_bot D h1] at ha; simp at ha; simp [ha]

/-- Membership in `A'` is detected componentwise. -/
lemma cmpL_mem_pieceSub {a : A} (ha : a ∈ subDGA D) (i : ℤ × ℤ) :
    cmpL 𝒜 i a ∈ pieceSub D i := by
  induction ha using Submodule.iSup_induction' with
  | mem j x hx =>
      by_cases hij : j = i
      · subst hij
        rwa [cmpL_of_mem_same 𝒜 (pieceSub_le_graded D j hx)]
      · rw [cmpL_of_mem_ne 𝒜 (pieceSub_le_graded D j hx) hij]
        exact Submodule.zero_mem _
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- Membership in `J` is detected componentwise. -/
lemma cmpL_mem_pieceIdeal {a : A} (ha : a ∈ idealDGA D) (i : ℤ × ℤ) :
    cmpL 𝒜 i a ∈ pieceIdeal D i := by
  induction ha using Submodule.iSup_induction' with
  | mem j x hx =>
      by_cases hij : j = i
      · subst hij
        rwa [cmpL_of_mem_same 𝒜 ((pieceIdeal_le_pieceSub D j).trans
          (pieceSub_le_graded D j) hx)]
      · rw [cmpL_of_mem_ne 𝒜 ((pieceIdeal_le_pieceSub D j).trans
          (pieceSub_le_graded D j) hx) hij]
        exact Submodule.zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

/-- A finite sum of coboundaries of elements of a submodule `P` is a coboundary of an element
of `P`. -/
lemma exists_primitive_sum {ι : Type*} {s : Finset ι} {f : ι → A} {P : Submodule k A}
    (h : ∀ i ∈ s, ∃ c ∈ P, D.d c = f i) : ∃ c ∈ P, D.d c = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, Submodule.zero_mem _, by simp⟩
  | insert i s hi ih =>
      obtain ⟨c₁, hc₁, hdc₁⟩ := h i (Finset.mem_insert_self i s)
      obtain ⟨c₂, hc₂, hdc₂⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
      refine ⟨c₁ + c₂, Submodule.add_mem _ hc₁ hc₂, ?_⟩
      rw [map_add, hdc₁, hdc₂, Finset.sum_insert hi]

end Construction

/-- Data exhibiting *strict formality* of a dg-algebra `(A, d)`:
a sub-dg-algebra `sub ⊆ A` quasi-isomorphic to `A`, together with a two-sided ideal
`ideal ⊆ sub` which is acyclic and contains `d sub`.  Thus the quotient `sub / ideal` is a
graded algebra with **zero** differential, and the zig-zag
`A ⊇ sub ↠ sub/ideal` consists of quasi-isomorphisms of dg-algebras. -/
structure StrictFormalityData (D : WeightedDGA 𝒜) where
  /-- The sub-dg-algebra. -/
  sub : Submodule k A
  /-- The acyclic ideal. -/
  idl : Submodule k A
  one_mem : (1 : A) ∈ sub
  mul_mem : ∀ a ∈ sub, ∀ b ∈ sub, a * b ∈ sub
  idl_le : idl ≤ sub
  mul_idl : ∀ a ∈ sub, ∀ b ∈ idl, a * b ∈ idl
  idl_mul : ∀ a ∈ idl, ∀ b ∈ sub, a * b ∈ idl
  /-- The differential vanishes on the quotient `sub / idl`. -/
  d_sub : ∀ a ∈ sub, D.d a ∈ idl
  /-- Every cocycle of `A` is cohomologous to a cocycle of `sub`. -/
  qis_surj : ∀ a, D.d a = 0 → ∃ z ∈ sub, D.d z = 0 ∧ ∃ c, a = z + D.d c
  /-- A cocycle of `sub` which bounds in `A` already bounds in `sub`. -/
  qis_inj : ∀ z ∈ sub, ∀ c : A, z = D.d c → ∃ c' ∈ sub, z = D.d c'
  /-- The ideal is acyclic. -/
  idl_acyclic : ∀ j ∈ idl, D.d j = 0 → ∃ j' ∈ idl, j = D.d j'

namespace StrictFormalityData

variable {D : WeightedDGA 𝒜} (F : StrictFormalityData D)

include F




end StrictFormalityData

section MainTheorem

variable (D : WeightedDGA 𝒜)

/-- **Purity implies formality.**  If the weight grading on the cohomology of a weight-graded
dg-algebra is pure (weight = cohomological degree), then the dg-algebra is formal: there is a
strict zig-zag `A ⊇ A' ↠ A'/J` of quasi-isomorphisms of dg-algebras with `A'/J` carrying the
zero differential.

In the rigid-analytic setting purity is exactly what the weight-monodromy conjecture supplies,
so this is the algebraic engine of the formality theorem. -/
noncomputable def formality_of_weight_purity (hpure : IsWeightPure D) :
    StrictFormalityData D where
  sub := subDGA D
  idl := idealDGA D
  one_mem := one_mem_subDGA D
  mul_mem := fun _ ha _ hb => subDGA_mul_mem D ha hb
  idl_le := idealDGA_le_subDGA D
  mul_idl := fun _ ha _ hb => mul_idealDGA_mem D ha hb
  idl_mul := fun _ ha _ hb => idealDGA_mul_mem D ha hb
  d_sub := fun a ha => d_subDGA_le_idealDGA D ⟨a, ha, rfl⟩
  qis_surj := by
    intro a ha
    classical
    set s := supp 𝒜 a with hs
    set t := s.filter (fun i => i.1 ≤ i.2) with ht
    set z := ∑ i ∈ t, cmpL 𝒜 i a with hz
    have hsplit : a = z + ∑ i ∈ s.filter (fun i => ¬ i.1 ≤ i.2), cmpL 𝒜 i a := by
      rw [hz, ht, Finset.sum_filter_add_sum_filter_not]
      exact (sum_cmpL 𝒜 a).symm
    have hzsub : z ∈ subDGA D := by
      refine Submodule.sum_mem _ fun i hi => ?_
      have hle : i.1 ≤ i.2 := (Finset.mem_filter.mp hi).2
      rcases lt_or_eq_of_le hle with h | h
      · exact mem_subDGA_of_lt D h (cmpL_mem 𝒜 a i)
      · exact mem_subDGA_of_diag D h (cmpL_mem 𝒜 a i) (D.cmpL_cocycle ha i)
    have hzd : D.d z = 0 := by
      rw [hz, map_sum]
      exact Finset.sum_eq_zero fun i _ => D.cmpL_cocycle ha i
    obtain ⟨c, -, hc⟩ : ∃ c ∈ (⊤ : Submodule k A), D.d c
        = ∑ i ∈ s.filter (fun i => ¬ i.1 ≤ i.2), cmpL 𝒜 i a := by
      refine exists_primitive_sum D fun i hi => ?_
      have hgt : i.2 < i.1 := by
        have := (Finset.mem_filter.mp hi).2; omega
      obtain ⟨c, _, hc⟩ := hpure i.1 i.2 (by omega) (cmpL 𝒜 i a)
        (by simpa using cmpL_mem 𝒜 a i) (D.cmpL_cocycle ha i)
      exact ⟨c, Submodule.mem_top, hc⟩
    exact ⟨z, hzsub, hzd, c, by rw [hc]; exact hsplit⟩
  qis_inj := by
    intro z hz c hc
    classical
    set s := supp 𝒜 c with hs
    set c' := ∑ i ∈ s.filter (fun i => i.1 < i.2), cmpL 𝒜 i c with hc'
    have hc'sub : c' ∈ subDGA D := by
      refine Submodule.sum_mem _ fun i hi => ?_
      exact mem_subDGA_of_lt D (Finset.mem_filter.mp hi).2 (cmpL_mem 𝒜 c i)
    refine ⟨c', hc'sub, ?_⟩
    have hvanish : ∀ i ∈ s.filter (fun i => ¬ i.1 < i.2), D.d (cmpL 𝒜 i c) = 0 := by
      intro i hi
      have hge : i.2 ≤ i.1 := by have := (Finset.mem_filter.mp hi).2; omega
      have hcomp : cmpL 𝒜 (i.1 + 1, i.2) z = D.d (cmpL 𝒜 i c) := by
        rw [hc]
        exact D.cmpL_d c i.1 i.2
      have : cmpL 𝒜 (i.1 + 1, i.2) z = 0 := by
        have hmem := cmpL_mem_pieceSub D hz (i.1 + 1, i.2)
        have hb : pieceSub D (i.1 + 1, i.2) = ⊥ := by
          have h1 : ¬ ((i.1 + 1 : ℤ) < i.2) := by omega
          have h2 : ¬ ((i.1 + 1 : ℤ) = i.2) := by omega
          simp [pieceSub, h1, h2]
        rw [hb] at hmem
        simpa using hmem
      rw [← hcomp, this]
    calc z = D.d c := hc
      _ = ∑ i ∈ s, D.d (cmpL 𝒜 i c) := by rw [← map_sum, sum_cmpL]
      _ = ∑ i ∈ s.filter (fun i => i.1 < i.2), D.d (cmpL 𝒜 i c)
            + ∑ i ∈ s.filter (fun i => ¬ i.1 < i.2), D.d (cmpL 𝒜 i c) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ = ∑ i ∈ s.filter (fun i => i.1 < i.2), D.d (cmpL 𝒜 i c) := by
          rw [Finset.sum_eq_zero hvanish, add_zero]
      _ = D.d c' := by rw [hc', map_sum]
  idl_acyclic := by
    intro j hj hdj
    classical
    have key : ∀ i : ℤ × ℤ, ∃ c ∈ idealDGA D, D.d c = cmpL 𝒜 i j := by
      intro i
      have hmem := cmpL_mem_pieceIdeal D hj i
      rcases lt_trichotomy i.1 i.2 with h1 | h1 | h1
      · obtain ⟨c, hcmem, hc⟩ := hpure i.1 i.2 (by omega) (cmpL 𝒜 i j)
          (by simpa using cmpL_mem 𝒜 j i) (D.cmpL_cocycle hdj i)
        exact ⟨c, mem_idealDGA_of_lt D (by simpa using (by omega : i.1 - 1 < i.2)) hcmem, hc⟩
      · have hne : ¬ i.1 < i.2 := by omega
        simp only [pieceIdeal, if_neg hne, if_pos h1] at hmem
        obtain ⟨c, hcmem, hc⟩ := hmem
        exact ⟨c, mem_idealDGA_of_lt D (by simpa using (by omega : i.1 - 1 < i.2)) hcmem, hc⟩
      · rw [pieceIdeal_eq_bot D h1] at hmem
        have : cmpL 𝒜 i j = 0 := by simpa using hmem
        exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    obtain ⟨c, hc, hdc⟩ := exists_primitive_sum (s := supp 𝒜 j) (f := fun i => cmpL 𝒜 i j)
      (P := idealDGA D) D (fun i _ => key i)
    exact ⟨c, hc, by rw [hdc, sum_cmpL]⟩


end MainTheorem

end WeightMonodromy


