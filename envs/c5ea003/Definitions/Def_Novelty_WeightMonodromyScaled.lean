-- Prove2me | Definitions.Def_Novelty_WeightMonodromyScaled
-- name    : Novelty_WeightMonodromyScaled
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:55:08.838525+00:00
-- url     : https://prove2.me/theorems/4842ff0d-8403-40fb-8567-acff7c8cd645
-- title:
--   Aether Catalog definitions — Novelty_WeightMonodromyScaled
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.WeightMonodromyScaled`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/WeightMonodromyScaled.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_WeightMonodromyFormality
/-
Copyright (c) 2026. Released under Apache 2.0 license.
-/

/-!
# Formality for arbitrary weight normalisations

`Catalog/Novelty/WeightMonodromyFormality.lean` proves that a weight-graded dg-algebra whose
cohomology is pure *with weight equal to the cohomological degree* is formal.  In arithmetic
practice the normalisation varies: with Tate twists the interesting weight of `H^n` is `2n`
rather than `n`, and comparison isomorphisms may rescale weights by any fixed positive factor.

This file removes the normalisation.  Fix an additive map `wt : ℤ →+ ℤ` with `0 < wt 1`
(equivalently `wt n = α n` with `α > 0`) and call a weight-graded dg-algebra `wt`-pure if its
cohomology in bidegree `(n, w)` vanishes for `w ≠ wt n`.  The main theorem
`formality_of_pureFor` produces the same strict formality zig-zag `A ⊇ A' ↠ A'/J` in this
generality, with `A'` the weight-wise canonical truncation *along the line `w = wt n`*.

The case `wt = id` recovers `formality_of_weight_purity` (see `isPureFor_id_iff`).

Note that when `α > 1` the line `w = wt n` misses most weights: for a weight `w` outside the
image of `wt` the whole weight-`w` subcomplex is acyclic and the truncation must discard it
entirely.  This is why the pieces below are indexed by pairs *(degree, diagonal index)* rather
than by bidegrees.
-/

namespace WeightMonodromy

open scoped Classical

variable {k A : Type*} [Field k] [Ring A] [Algebra k A]
variable {𝒜 : ℤ × ℤ → Submodule k A} [GradedAlgebra 𝒜]

section WtBasic

variable (wt : ℤ →+ ℤ)

lemma wt_apply (m : ℤ) : wt m = m * wt 1 := by
  have h := map_zsmul wt m (1 : ℤ)
  simpa [zsmul_eq_mul] using h

lemma wt_strictMono (hwt : 0 < wt 1) : StrictMono wt := by
  intro a b hab
  rw [wt_apply wt a, wt_apply wt b]
  exact mul_lt_mul_of_pos_right hab hwt

lemma wt_injective (hwt : 0 < wt 1) : Function.Injective wt :=
  (wt_strictMono wt hwt).injective

end WtBasic

variable (D : WeightedDGA 𝒜) (wt : ℤ →+ ℤ)

/-- Purity of the weight grading along the line `w = wt n`: there is no cohomology in bidegree
`(n, w)` unless `w = wt n`, and the primitive can be chosen of the same weight. -/
def IsPureFor : Prop :=
  ∀ n w : ℤ, w ≠ wt n → ∀ a ∈ 𝒜 (n, w), D.d a = 0 → ∃ c ∈ 𝒜 (n - 1, w), D.d c = a


/-- Pieces of the truncated sub-dg-algebra, indexed by `(degree, diagonal index)`. -/
noncomputable def sPiece (q : ℤ × ℤ) : Submodule k A :=
  if q.1 < q.2 then 𝒜 (q.1, wt q.2)
  else if q.1 = q.2 then 𝒜 (q.1, wt q.2) ⊓ LinearMap.ker D.d
  else ⊥

/-- Pieces of the acyclic ideal, indexed by `(degree, diagonal index)`. -/
noncomputable def iPiece (q : ℤ × ℤ) : Submodule k A :=
  if q.1 < q.2 then 𝒜 (q.1, wt q.2)
  else if q.1 = q.2 then (𝒜 (q.1 - 1, wt q.2)).map D.d
  else ⊥

/-- The `wt`-truncated sub-dg-algebra of `A`. -/
noncomputable def sSub : Submodule k A := ⨆ q, sPiece D wt q

/-- The acyclic ideal of `sSub`. -/
noncomputable def sIdeal : Submodule k A := ⨆ q, iPiece D wt q

lemma sPiece_le_graded (q : ℤ × ℤ) : sPiece D wt q ≤ 𝒜 (q.1, wt q.2) := by
  unfold sPiece
  split_ifs
  · exact le_rfl
  · exact inf_le_left
  · exact bot_le

lemma iPiece_le_sPiece (q : ℤ × ℤ) : iPiece D wt q ≤ sPiece D wt q := by
  unfold iPiece sPiece
  split_ifs with h1 h2
  · exact le_rfl
  · rintro x ⟨c, hc, rfl⟩
    refine ⟨?_, ?_⟩
    · have hm := D.d_mem (q.1 - 1, wt q.2) c hc
      simpa [show q.1 - 1 + 1 = q.1 from by omega] using hm
    · simp [LinearMap.mem_ker, D.d_comp_d]
  · exact bot_le

lemma iPiece_le_graded (q : ℤ × ℤ) : iPiece D wt q ≤ 𝒜 (q.1, wt q.2) :=
  (iPiece_le_sPiece D wt q).trans (sPiece_le_graded D wt q)

lemma sIdeal_le_sSub : sIdeal D wt ≤ sSub D wt :=
  iSup_mono fun q => iPiece_le_sPiece D wt q

lemma sPiece_eq_bot {q : ℤ × ℤ} (h : q.2 < q.1) : sPiece D wt q = ⊥ := by
  have h1 : ¬ q.1 < q.2 := by omega
  have h2 : ¬ q.1 = q.2 := by omega
  simp [sPiece, h1, h2]

lemma iPiece_eq_bot {q : ℤ × ℤ} (h : q.2 < q.1) : iPiece D wt q = ⊥ := by
  have h1 : ¬ q.1 < q.2 := by omega
  have h2 : ¬ q.1 = q.2 := by omega
  simp [iPiece, h1, h2]

lemma mem_sSub_of_lt {n m : ℤ} (h : n < m) {a : A} (ha : a ∈ 𝒜 (n, wt m)) : a ∈ sSub D wt := by
  refine le_iSup (sPiece D wt) (n, m) ?_
  simpa [sPiece, h] using ha

lemma mem_sSub_of_diag {m : ℤ} {a : A} (ha : a ∈ 𝒜 (m, wt m)) (hd : D.d a = 0) :
    a ∈ sSub D wt := by
  refine le_iSup (sPiece D wt) (m, m) ?_
  simp only [sPiece, lt_irrefl, if_false]
  exact ⟨ha, by simpa using hd⟩

lemma mem_sIdeal_of_lt {n m : ℤ} (h : n < m) {a : A} (ha : a ∈ 𝒜 (n, wt m)) :
    a ∈ sIdeal D wt := by
  refine le_iSup (iPiece D wt) (n, m) ?_
  simpa [iPiece, h] using ha

lemma mem_sIdeal_of_diag {m : ℤ} {c : A} (hc : c ∈ 𝒜 (m - 1, wt m)) :
    D.d c ∈ sIdeal D wt := by
  refine le_iSup (iPiece D wt) (m, m) ?_
  simp only [iPiece, lt_irrefl, if_false]
  exact ⟨c, hc, rfl⟩

/-! ### Multiplicative structure -/

lemma sPiece_mul_le (q q' : ℤ × ℤ) : sPiece D wt q * sPiece D wt q' ≤ sSub D wt := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 (q.1, wt q.2) := sPiece_le_graded D wt q ha
  have hgj : b ∈ 𝒜 (q'.1, wt q'.2) := sPiece_le_graded D wt q' hb
  have hab : a * b ∈ 𝒜 (q.1 + q'.1, wt (q.2 + q'.2)) := by
    have := SetLike.mul_mem_graded hgi hgj
    simpa [Prod.mk_add_mk, map_add] using this
  rcases lt_trichotomy q.1 q.2 with h1 | h1 | h1
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sSub_of_lt D wt (by omega) hab
    · exact mem_sSub_of_lt D wt (by omega) hab
    · rw [sPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sSub_of_lt D wt (by omega) hab
    · have hda : D.d a = 0 := by
        have hne : ¬ q.1 < q.2 := by omega
        simp only [sPiece, if_neg hne, if_pos h1] at ha
        simpa using ha.2
      have hdb : D.d b = 0 := by
        have hne : ¬ q'.1 < q'.2 := by omega
        simp only [sPiece, if_neg hne, if_pos h2] at hb
        simpa using hb.2
      have heq : q.1 + q'.1 = q.2 + q'.2 := by omega
      refine mem_sSub_of_diag D wt (m := q.2 + q'.2) (by rwa [heq] at hab) ?_
      rw [D.leibniz q.1 (wt q.2) a b hgi, hda, hdb]
      simp
    · rw [sPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rw [sPiece_eq_bot D wt h1] at ha; simp at ha; simp [ha]

lemma sSub_mul_mem {a b : A} (ha : a ∈ sSub D wt) (hb : b ∈ sSub D wt) :
    a * b ∈ sSub D wt := by
  have hle : sSub D wt * sSub D wt ≤ sSub D wt := by
    unfold sSub
    rw [Submodule.iSup_mul]
    refine iSup_le fun q => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun q' => sPiece_mul_le D wt q q'
  exact hle (Submodule.mul_mem_mul ha hb)

lemma one_mem_sSub : (1 : A) ∈ sSub D wt := by
  have h1 : (1 : A) ∈ 𝒜 ((0 : ℤ), wt 0) := by simpa using SetLike.one_mem_graded 𝒜
  exact mem_sSub_of_diag D wt (m := 0) h1 D.d_one

lemma iPiece_mul_le (q q' : ℤ × ℤ) : iPiece D wt q * sPiece D wt q' ≤ sIdeal D wt := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 (q.1, wt q.2) := iPiece_le_graded D wt q ha
  have hgj : b ∈ 𝒜 (q'.1, wt q'.2) := sPiece_le_graded D wt q' hb
  have hab : a * b ∈ 𝒜 (q.1 + q'.1, wt (q.2 + q'.2)) := by
    have := SetLike.mul_mem_graded hgi hgj
    simpa [Prod.mk_add_mk, map_add] using this
  rcases lt_trichotomy q.1 q.2 with h1 | h1 | h1
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · rw [sPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · obtain ⟨c, hc, rfl⟩ : ∃ c ∈ 𝒜 (q.1 - 1, wt q.2), D.d c = a := by
        have hne : ¬ q.1 < q.2 := by omega
        simp only [iPiece, if_neg hne, if_pos h1] at ha
        obtain ⟨c, hc, hcc⟩ := ha
        exact ⟨c, hc, hcc⟩
      have hdb : D.d b = 0 := by
        have hne : ¬ q'.1 < q'.2 := by omega
        simp only [sPiece, if_neg hne, if_pos h2] at hb
        simpa using hb.2
      have hcb : c * b ∈ 𝒜 (q.2 + q'.2 - 1, wt (q.2 + q'.2)) := by
        have := SetLike.mul_mem_graded hc hgj
        simpa [Prod.mk_add_mk, map_add,
          show q.1 - 1 + q'.1 = q.2 + q'.2 - 1 from by omega] using this
      have hkey : D.d c * b = D.d (c * b) := by
        rw [D.leibniz (q.1 - 1) (wt q.2) c b hc, hdb]
        simp
      rw [hkey]
      exact mem_sIdeal_of_diag D wt hcb
    · rw [sPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rw [iPiece_eq_bot D wt h1] at ha; simp at ha; simp [ha]

lemma mul_iPiece_le (q q' : ℤ × ℤ) : sPiece D wt q * iPiece D wt q' ≤ sIdeal D wt := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  have hgi : a ∈ 𝒜 (q.1, wt q.2) := sPiece_le_graded D wt q ha
  have hgj : b ∈ 𝒜 (q'.1, wt q'.2) := iPiece_le_graded D wt q' hb
  have hab : a * b ∈ 𝒜 (q.1 + q'.1, wt (q.2 + q'.2)) := by
    have := SetLike.mul_mem_graded hgi hgj
    simpa [Prod.mk_add_mk, map_add] using this
  rcases lt_trichotomy q.1 q.2 with h1 | h1 | h1
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · rw [iPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rcases lt_trichotomy q'.1 q'.2 with h2 | h2 | h2
    · exact mem_sIdeal_of_lt D wt (by omega) hab
    · obtain ⟨c, hc, rfl⟩ : ∃ c ∈ 𝒜 (q'.1 - 1, wt q'.2), D.d c = b := by
        have hne : ¬ q'.1 < q'.2 := by omega
        simp only [iPiece, if_neg hne, if_pos h2] at hb
        obtain ⟨c, hc, hcc⟩ := hb
        exact ⟨c, hc, hcc⟩
      have hda : D.d a = 0 := by
        have hne : ¬ q.1 < q.2 := by omega
        simp only [sPiece, if_neg hne, if_pos h1] at ha
        simpa using ha.2
      have hac : a * c ∈ 𝒜 (q.2 + q'.2 - 1, wt (q.2 + q'.2)) := by
        have := SetLike.mul_mem_graded hgi hc
        simpa [Prod.mk_add_mk, map_add,
          show q.1 + (q'.1 - 1) = q.2 + q'.2 - 1 from by omega] using this
      have hkey : a * D.d c = (D.sgn q.1)⁻¹ • D.d (a * c) := by
        rw [D.leibniz q.1 (wt q.2) a c hgi, hda, zero_mul, zero_add, smul_smul,
          inv_mul_cancel₀ (D.sgn_ne_zero q.1), one_smul]
      rw [hkey]
      exact Submodule.smul_mem _ _ (mem_sIdeal_of_diag D wt hac)
    · rw [iPiece_eq_bot D wt h2] at hb; simp at hb; simp [hb]
  · rw [sPiece_eq_bot D wt h1] at ha; simp at ha; simp [ha]

lemma sIdeal_mul_mem {a b : A} (ha : a ∈ sIdeal D wt) (hb : b ∈ sSub D wt) :
    a * b ∈ sIdeal D wt := by
  have hle : sIdeal D wt * sSub D wt ≤ sIdeal D wt := by
    unfold sIdeal sSub
    rw [Submodule.iSup_mul]
    refine iSup_le fun q => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun q' => iPiece_mul_le D wt q q'
  exact hle (Submodule.mul_mem_mul ha hb)

lemma mul_sIdeal_mem {a b : A} (ha : a ∈ sSub D wt) (hb : b ∈ sIdeal D wt) :
    a * b ∈ sIdeal D wt := by
  have hle : sSub D wt * sIdeal D wt ≤ sIdeal D wt := by
    unfold sIdeal sSub
    rw [Submodule.iSup_mul]
    refine iSup_le fun q => ?_
    rw [Submodule.mul_iSup]
    exact iSup_le fun q' => mul_iPiece_le D wt q q'
  exact hle (Submodule.mul_mem_mul ha hb)

lemma d_sSub_le_sIdeal : Submodule.map D.d (sSub D wt) ≤ sIdeal D wt := by
  unfold sSub
  rw [Submodule.map_iSup]
  refine iSup_le fun q => ?_
  rintro x ⟨a, ha, rfl⟩
  rcases lt_trichotomy q.1 q.2 with h1 | h1 | h1
  · have hga : a ∈ 𝒜 (q.1, wt q.2) := by simpa [sPiece, h1] using ha
    have hda : D.d a ∈ 𝒜 (q.1 + 1, wt q.2) := by
      have := D.d_mem (q.1, wt q.2) a hga
      simpa using this
    rcases lt_or_eq_of_le (by omega : q.1 + 1 ≤ q.2) with h2 | h2
    · exact mem_sIdeal_of_lt D wt h2 hda
    · refine mem_sIdeal_of_diag D wt (m := q.2) ?_
      simpa [show q.2 - 1 = q.1 from by omega] using hga
  · have hz : D.d a = 0 := by
      have hne : ¬ q.1 < q.2 := by omega
      simp only [sPiece, if_neg hne, if_pos h1] at ha
      simpa using ha.2
    simp [hz]
  · rw [sPiece_eq_bot D wt h1] at ha; simp at ha; simp [ha]

/-! ### Componentwise detection -/

lemma cmpL_mem_sPiece (hwt : 0 < wt 1) {a : A} (ha : a ∈ sSub D wt) (q : ℤ × ℤ) :
    cmpL 𝒜 (q.1, wt q.2) a ∈ sPiece D wt q := by
  induction ha using Submodule.iSup_induction' with
  | mem q' x hx =>
      by_cases hq : q' = q
      · subst hq
        rwa [cmpL_of_mem_same 𝒜 (sPiece_le_graded D wt q' hx)]
      · rw [cmpL_of_mem_ne 𝒜 (sPiece_le_graded D wt q' hx) ?_]
        · exact Submodule.zero_mem _
        · intro hcon
          simp only [Prod.mk.injEq] at hcon
          exact hq (Prod.ext hcon.1 (wt_injective wt hwt hcon.2))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

lemma cmpL_mem_iPiece (hwt : 0 < wt 1) {a : A} (ha : a ∈ sIdeal D wt) (q : ℤ × ℤ) :
    cmpL 𝒜 (q.1, wt q.2) a ∈ iPiece D wt q := by
  induction ha using Submodule.iSup_induction' with
  | mem q' x hx =>
      by_cases hq : q' = q
      · subst hq
        rwa [cmpL_of_mem_same 𝒜 (iPiece_le_graded D wt q' hx)]
      · rw [cmpL_of_mem_ne 𝒜 (iPiece_le_graded D wt q' hx) ?_]
        · exact Submodule.zero_mem _
        · intro hcon
          simp only [Prod.mk.injEq] at hcon
          exact hq (Prod.ext hcon.1 (wt_injective wt hwt hcon.2))
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

lemma cmpL_eq_zero_of_notMem_range_sSub {a : A} (ha : a ∈ sSub D wt) {i : ℤ × ℤ}
    (hi : ∀ m : ℤ, i.2 ≠ wt m) : cmpL 𝒜 i a = 0 := by
  induction ha using Submodule.iSup_induction' with
  | mem q' x hx =>
      refine cmpL_of_mem_ne 𝒜 (sPiece_le_graded D wt q' hx) ?_
      intro hcon
      exact hi q'.2 (congrArg Prod.snd hcon).symm
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]

lemma cmpL_eq_zero_of_notMem_range_sIdeal {a : A} (ha : a ∈ sIdeal D wt) {i : ℤ × ℤ}
    (hi : ∀ m : ℤ, i.2 ≠ wt m) : cmpL 𝒜 i a = 0 :=
  cmpL_eq_zero_of_notMem_range_sSub D wt (sIdeal_le_sSub D wt ha) hi

/-! ### The main theorem -/

/-- **Purity implies formality, for any positive weight normalisation.**  If the cohomology of
the weight-graded dg-algebra `A` is concentrated on the line `w = wt n` (with `wt n = α n`,
`α > 0`), then `A` is formal: `A ⊇ sSub ↠ sSub / sIdeal` is a zig-zag of quasi-isomorphisms of
dg-algebras whose right-hand term carries the zero differential. -/
noncomputable def formality_of_pureFor (hwt : 0 < wt 1) (hpure : IsPureFor D wt) :
    StrictFormalityData D where
  sub := sSub D wt
  idl := sIdeal D wt
  one_mem := one_mem_sSub D wt
  mul_mem := fun _ ha _ hb => sSub_mul_mem D wt ha hb
  idl_le := sIdeal_le_sSub D wt
  mul_idl := fun _ ha _ hb => mul_sIdeal_mem D wt ha hb
  idl_mul := fun _ ha _ hb => sIdeal_mul_mem D wt ha hb
  d_sub := fun a ha => d_sSub_le_sIdeal D wt ⟨a, ha, rfl⟩
  qis_surj := by
    intro a ha
    classical
    set s := supp 𝒜 a with hs
    set P : ℤ × ℤ → Prop := fun i => ∃ m : ℤ, i.2 = wt m ∧ i.1 ≤ m with hP
    set z := ∑ i ∈ s.filter P, cmpL 𝒜 i a with hz
    have hsplit : a = z + ∑ i ∈ s.filter (fun i => ¬ P i), cmpL 𝒜 i a := by
      rw [hz, Finset.sum_filter_add_sum_filter_not]
      exact (sum_cmpL 𝒜 a).symm
    have hzsub : z ∈ sSub D wt := by
      refine Submodule.sum_mem _ fun i hi => ?_
      obtain ⟨m, hm, hle⟩ := (Finset.mem_filter.mp hi).2
      have hmem : cmpL 𝒜 i a ∈ 𝒜 (i.1, wt m) := by
        have := cmpL_mem 𝒜 a i
        rwa [show (i.1, wt m) = i from Prod.ext rfl hm.symm]
      rcases lt_or_eq_of_le hle with h | h
      · exact mem_sSub_of_lt D wt h hmem
      · subst h
        exact mem_sSub_of_diag D wt hmem (D.cmpL_cocycle ha i)
    have hzd : D.d z = 0 := by
      rw [hz, map_sum]
      exact Finset.sum_eq_zero fun i _ => D.cmpL_cocycle ha i
    obtain ⟨c, -, hc⟩ : ∃ c ∈ (⊤ : Submodule k A), D.d c
        = ∑ i ∈ s.filter (fun i => ¬ P i), cmpL 𝒜 i a := by
      refine exists_primitive_sum D fun i hi => ?_
      have hnp : ¬ P i := (Finset.mem_filter.mp hi).2
      have hne : i.2 ≠ wt i.1 := by
        intro hcon
        exact hnp ⟨i.1, hcon, le_rfl⟩
      obtain ⟨c, -, hc⟩ := hpure i.1 i.2 hne (cmpL 𝒜 i a)
        (by simpa using cmpL_mem 𝒜 a i) (D.cmpL_cocycle ha i)
      exact ⟨c, Submodule.mem_top, hc⟩
    exact ⟨z, hzsub, hzd, c, by rw [hc]; exact hsplit⟩
  qis_inj := by
    intro z hz c hc
    classical
    set s := supp 𝒜 c with hs
    set Q : ℤ × ℤ → Prop := fun i => ∃ m : ℤ, i.2 = wt m ∧ i.1 < m with hQ
    set c' := ∑ i ∈ s.filter Q, cmpL 𝒜 i c with hc'
    have hc'sub : c' ∈ sSub D wt := by
      refine Submodule.sum_mem _ fun i hi => ?_
      obtain ⟨m, hm, hlt⟩ := (Finset.mem_filter.mp hi).2
      refine mem_sSub_of_lt D wt hlt ?_
      have := cmpL_mem 𝒜 c i
      rwa [show (i.1, wt m) = i from Prod.ext rfl hm.symm]
    refine ⟨c', hc'sub, ?_⟩
    have hvanish : ∀ i ∈ s.filter (fun i => ¬ Q i), D.d (cmpL 𝒜 i c) = 0 := by
      intro i hi
      have hnq : ¬ Q i := (Finset.mem_filter.mp hi).2
      have hcomp : cmpL 𝒜 (i.1 + 1, i.2) z = D.d (cmpL 𝒜 i c) := by
        rw [hc]; exact D.cmpL_d c i.1 i.2
      have hzero : cmpL 𝒜 (i.1 + 1, i.2) z = 0 := by
        by_cases hex : ∃ m : ℤ, i.2 = wt m
        · obtain ⟨m, hm⟩ := hex
          have hge : m ≤ i.1 := by
            by_contra hlt
            exact hnq ⟨m, hm, by omega⟩
          have hmem := cmpL_mem_sPiece D wt hwt hz (i.1 + 1, m)
          have hb : sPiece D wt (i.1 + 1, m) = ⊥ :=
            sPiece_eq_bot D wt (by simpa using (by omega : m < i.1 + 1))
          rw [hb] at hmem
          have : cmpL 𝒜 (i.1 + 1, wt m) z = 0 := by simpa using hmem
          rwa [← hm] at this
        · push_neg at hex
          exact cmpL_eq_zero_of_notMem_range_sSub D wt hz (by simpa using hex)
      rw [← hcomp, hzero]
    calc z = D.d c := hc
      _ = ∑ i ∈ s, D.d (cmpL 𝒜 i c) := by rw [← map_sum, sum_cmpL]
      _ = ∑ i ∈ s.filter Q, D.d (cmpL 𝒜 i c)
            + ∑ i ∈ s.filter (fun i => ¬ Q i), D.d (cmpL 𝒜 i c) :=
          (Finset.sum_filter_add_sum_filter_not _ _ _).symm
      _ = ∑ i ∈ s.filter Q, D.d (cmpL 𝒜 i c) := by
          rw [Finset.sum_eq_zero hvanish, add_zero]
      _ = D.d c' := by rw [hc', map_sum]
  idl_acyclic := by
    intro j hj hdj
    classical
    have key : ∀ i : ℤ × ℤ, ∃ c ∈ sIdeal D wt, D.d c = cmpL 𝒜 i j := by
      intro i
      by_cases hex : ∃ m : ℤ, i.2 = wt m
      · obtain ⟨m, hm⟩ := hex
        have hmem : cmpL 𝒜 (i.1, wt m) j ∈ iPiece D wt (i.1, m) :=
          cmpL_mem_iPiece D wt hwt hj (i.1, m)
        rw [show (i.1, wt m) = i from Prod.ext rfl hm.symm] at hmem
        rcases lt_trichotomy i.1 m with h1 | h1 | h1
        · have hne : i.2 ≠ wt i.1 := by
            rw [hm]
            exact fun hcon => absurd (wt_injective wt hwt hcon) (by omega)
          obtain ⟨c, hcmem, hc⟩ := hpure i.1 i.2 hne (cmpL 𝒜 i j)
            (by simpa using cmpL_mem 𝒜 j i) (D.cmpL_cocycle hdj i)
          refine ⟨c, mem_sIdeal_of_lt D wt (n := i.1 - 1) (m := m) (by omega) ?_, hc⟩
          rwa [← hm]
        · subst h1
          simp only [iPiece, lt_irrefl, if_false] at hmem
          obtain ⟨c, hcmem, hc⟩ := hmem
          exact ⟨c, mem_sIdeal_of_lt D wt (n := i.1 - 1) (m := i.1) (by omega) hcmem, hc⟩
        · have hb : iPiece D wt (i.1, m) = ⊥ :=
            iPiece_eq_bot D wt (by simpa using h1)
          rw [hb] at hmem
          have : cmpL 𝒜 i j = 0 := by simpa using hmem
          exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
      · push_neg at hex
        have : cmpL 𝒜 i j = 0 :=
          cmpL_eq_zero_of_notMem_range_sIdeal D wt hj (by simpa using hex)
        exact ⟨0, Submodule.zero_mem _, by simp [this]⟩
    obtain ⟨c, hc, hdc⟩ := exists_primitive_sum (s := supp 𝒜 j) (f := fun i => cmpL 𝒜 i j)
      (P := sIdeal D wt) D (fun i _ => key i)
    exact ⟨c, hc, by rw [hdc, sum_cmpL]⟩



end WeightMonodromy


