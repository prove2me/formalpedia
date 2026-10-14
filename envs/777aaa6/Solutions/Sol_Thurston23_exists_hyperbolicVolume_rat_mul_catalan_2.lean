-- Prove2me | solution 2 for Thurston23.exists_hyperbolicVolume_rat_mul_catalan
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-13T17:13:12.976252+00:00
-- url     : https://prove2.me/submissions/93832ede-707f-4975-be5d-53e8f7f77e91

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_picard
import Theorems.Thm_Thurston23_isKleinian_gammaTwoI
import Theorems.Thm_Thurston23_index_gammaTwoIEff
import Theorems.Thm_Thurston23_isFundamentalDomain_halfBox
import Theorems.Thm_Thurston23_hvol_halfBox_eq_ofReal_integral
import Theorems.Thm_CatalanLogSin_integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three

/-!
A hyperbolic `3`-manifold whose volume is a rational multiple of Catalan's constant: the
manifold `ℍ³/Γ(2 + i)`, of volume `20 G`.

The reduction: `Γ(2 + i)` is Kleinian (`isKleinian_gammaTwoI`); the closed half box is a
fundamental domain for the Picard group acting effectively (`isFundamentalDomain_halfBox`),
so by the first milestone's counting lemma a fundamental domain for `Γ(2 + i)` has
`[PicardEff : Γ(2 + i)] = 60` (`index_gammaTwoIEff`) times its volume; and that volume is
`-∫₀^{π/4} log (1 - 1/(4 cos²θ)) dθ` (`hvol_halfBox_eq_ofReal_integral`), which equals `G/3`
(`CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three`). The bridge from the effective quotient
back to `Γ(2 + i)` itself is legitimate because `Γ(2 + i) → PicardEff` is injective: an element
of `Γ(2 + i)` acting trivially fixes a point, so it is the identity by freeness.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

section FundamentalDomains

open Pointwise

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] [MeasurableSpace X]
  {μ : Measure X} [SMulInvariantMeasure Γ X μ] [MeasurableConstSMul Γ X]

/-- `Γ ⧸ S` is a `def` wrapper around `Quotient`, so the generic instance for
quotients of a countable type does not fire on it. -/
instance instCountableQuotientGroup [Countable Γ] (S : Subgroup Γ) : Countable (Γ ⧸ S) :=
  Quotient.countable

/-- If `F` is a fundamental domain for `Γ` and `S ≤ Γ`, then the union of the translates
of `F` by the inverses of a set of representatives of `Γ ⧸ S` is a fundamental domain
for `S`. This is the geometric content of Milestone 1: a fundamental domain for a
subgroup is assembled from one copy of `F` per coset. -/
theorem isFundamentalDomain_iUnion_out [Countable Γ] {F : Set X}
    (hF : IsFundamentalDomain Γ F μ) (S : Subgroup Γ) :
    IsFundamentalDomain S (⋃ q : Γ ⧸ S, (Quotient.out q)⁻¹ • F) μ where
  nullMeasurableSet :=
    NullMeasurableSet.iUnion fun q => hF.nullMeasurableSet_smul _
  ae_covers := by
    filter_upwards [hF.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    have hmem : (Quotient.out ((g : Γ ⧸ S)))⁻¹ * g ∈ S := by
      have := QuotientGroup.eq.mp (QuotientGroup.out_eq' (g : Γ ⧸ S))
      simpa using this
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨(g : Γ ⧸ S), ?_⟩⟩
    show ((Quotient.out ((g : Γ ⧸ S)))⁻¹ * g) • x ∈ _
    rw [mul_smul]
    exact Set.smul_mem_smul_set hg
  aedisjoint := by
    intro h₁ h₂ hne
    have hsmul : ∀ (h : S) (s : Set X), h • s = ((h : Γ)) • s := fun _ _ => rfl
    show μ (h₁ • _ ∩ h₂ • _) = 0
    rw [hsmul, hsmul]
    simp only [Set.smul_set_iUnion, smul_smul, Set.iUnion_inter, Set.inter_iUnion]
    refine measure_iUnion_null fun q => measure_iUnion_null fun r => hF.aedisjoint ?_
    intro hcontra
    apply hne
    have key : ((h₂ : Γ))⁻¹ * (h₁ : Γ) = (Quotient.out q)⁻¹ * (Quotient.out r) := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hcontra, inv_mul_cancel_right]
    have hmem : (Quotient.out q)⁻¹ * (Quotient.out r) ∈ S :=
      key ▸ S.mul_mem (S.inv_mem h₂.2) h₁.2
    have hqr : q = r := by
      have h := QuotientGroup.eq.mpr hmem
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at h
    subst hqr
    exact Subtype.ext (mul_right_cancel hcontra)

/-- **Milestone 1 in general form.** If `S` has finite index in `Γ`, a fundamental domain
for `S` has `S.index` times the measure of a fundamental domain for `Γ`. -/
theorem measure_eq_index_smul [Countable Γ] (S : Subgroup Γ) (hS : 0 < S.index)
    {F FS : Set X} (hF : IsFundamentalDomain Γ F μ) (hFS : IsFundamentalDomain S FS μ) :
    μ FS = S.index • μ F := by
  haveI : S.FiniteIndex := ⟨hS.ne'⟩
  haveI : Finite (Γ ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  haveI : Fintype (Γ ⧸ S) := Fintype.ofFinite _
  have hd : Pairwise
      (Function.onFun (AEDisjoint μ) (fun q : Γ ⧸ S => (Quotient.out q)⁻¹ • F)) :=
    fun q r hqr => hF.aedisjoint fun h => hqr (Quotient.out_injective (inv_injective h))
  have hm : ∀ q : Γ ⧸ S, NullMeasurableSet ((Quotient.out q)⁻¹ • F) μ :=
    fun q => hF.nullMeasurableSet_smul _
  rw [hFS.measure_eq (isFundamentalDomain_iUnion_out hF S), measure_iUnion₀ hd hm]
  simp only [measure_smul, tsum_fintype, Finset.sum_const, Finset.card_univ]
  show _ = Nat.card (Γ ⧸ S) • μ F
  rw [Nat.card_eq_fintype_card]

end FundamentalDomains


/-- Every nonempty open subset of `H3` has positive hyperbolic volume. Lebesgue
measure has this property, it survives restriction to the open half-space, and
the density `t⁻³` vanishes nowhere, so Lebesgue measure is absolutely continuous
with respect to `hvol`. -/
instance : hvol.IsOpenPosMeasure := by
  haveI : ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val : Measure H3).IsOpenPosMeasure :=
    .comap _ isOpen_upperHalfSpace.isOpenEmbedding_subtypeVal
  have hmeas : Measurable fun p : H3 => ENNReal.ofReal ((p.1 2) ^ (3 : ℕ))⁻¹ :=
    (((measurable_pi_apply 2).comp measurable_subtype_coe).pow_const 3).inv.ennreal_ofReal
  show (((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
    fun p : H3 => ENNReal.ofReal ((p.1 2) ^ (3 : ℕ))⁻¹).IsOpenPosMeasure
  exact (withDensity_absolutelyContinuous' hmeas.aemeasurable
    (ae_of_all _ fun p => (ENNReal.ofReal_pos.2 (inv_pos.2 (pow_pos p.2 3))).ne')).isOpenPosMeasure

/-- A nonempty open subset of `H3` has positive hyperbolic volume. -/
theorem hvol_pos_of_isOpen {U : Set H3} (hU : IsOpen U) (hne : U.Nonempty) : 0 < hvol U :=
  hU.measure_pos hvol hne


section Final

open Set MatrixGroups Quaternion Pointwise

instance : Countable GaussianInt :=
  (show Function.Injective (fun z : GaussianInt => (z.re, z.im)) from
    fun _ _ h => Zsqrtd.ext (congrArg Prod.fst h) (congrArg Prod.snd h)).countable

instance : Countable SL(2, GaussianInt) :=
  (show Function.Injective (fun (g : SL(2, GaussianInt)) (i j : Fin 2) => g i j) from
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j).countable

instance : Countable picard := by
  change Countable (Set.range (Matrix.SpecialLinearGroup.map GaussianInt.toComplex))
  exact (Set.countable_range _).to_subtype

instance : SMulInvariantMeasure PicardEff H3 hvol :=
  ⟨fun q _ hs => (PicardEff.measurePreserving q).measure_preimage hs.nullMeasurableSet⟩

instance : MeasurableConstSMul PicardEff H3 :=
  ⟨fun q => (PicardEff.measurePreserving q).measurable⟩

/-- An element of `Γ(2+i)` acting trivially is the identity: the action is free. -/
theorem eq_one_of_mem_gammaTwoI_of_smul_eq {g : SL(2, ℂ)} (hg : g ∈ gammaTwoI)
    (h : ∀ p : H3, g • p = p) : g = 1 := by
  by_contra hne
  exact isKleinian_gammaTwoI.free ⟨g, hg⟩ (fun h1 => hne (congrArg Subtype.val h1)) basepoint
    (h basepoint)

/-- `Γ(2+i)` injects into the effective quotient. -/
theorem gammaTwoI_toEff_injective :
    Function.Injective (fun γ : gammaTwoI =>
      (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaTwoI_le_picard γ.2⟩ : PicardEff)) := by
  intro γ₁ γ₂ h
  have hmem : (⟨(γ₁ : SL(2, ℂ)), gammaTwoI_le_picard γ₁.2⟩ : picard)⁻¹ *
      ⟨(γ₂ : SL(2, ℂ)), gammaTwoI_le_picard γ₂.2⟩ ∈ picardKer := QuotientGroup.eq.mp h
  rw [picardKer, MonoidHom.mem_ker] at hmem
  have htriv : ∀ p : H3, ((γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ))) • p = p := by
    intro p
    have := congrArg (fun e : Equiv.Perm H3 => e p) hmem
    simpa using this
  have hmul : (γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ)) ∈ gammaTwoI :=
    gammaTwoI.mul_mem (gammaTwoI.inv_mem γ₁.2) γ₂.2
  have hone := eq_one_of_mem_gammaTwoI_of_smul_eq hmul htriv
  exact Subtype.ext (inv_mul_eq_one.1 hone)

/-- A fundamental domain for the image of `Γ(2+i)` is one for `Γ(2+i)` itself. -/
theorem isFundamentalDomain_of_eff {F : Set H3}
    (h : IsFundamentalDomain gammaTwoIEff F hvol) : IsFundamentalDomain gammaTwoI F hvol := by
  refine ⟨h.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨g, hg, hgq⟩ := Subgroup.mem_map.1 q.2
    refine ⟨⟨(g : SL(2, ℂ)), Subgroup.mem_subgroupOf.1 hg⟩, ?_⟩
    have : ((g : picard) : PicardEff) = (q : PicardEff) := hgq
    show (g : SL(2, ℂ)) • x ∈ F
    have hq' : (q : PicardEff) • x ∈ F := hq
    rw [← this] at hq'
    exact hq'
  · intro γ₁ γ₂ hne
    have hinj := gammaTwoI_toEff_injective
    have hne' : (QuotientGroup.mk ⟨(γ₁ : SL(2, ℂ)), gammaTwoI_le_picard γ₁.2⟩ : PicardEff) ≠
        QuotientGroup.mk ⟨(γ₂ : SL(2, ℂ)), gammaTwoI_le_picard γ₂.2⟩ := fun h' => hne (hinj h')
    have hmem : ∀ γ : gammaTwoI,
        (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaTwoI_le_picard γ.2⟩ : PicardEff) ∈
          gammaTwoIEff := by
      intro γ
      exact Subgroup.mem_map.2 ⟨⟨(γ : SL(2, ℂ)), gammaTwoI_le_picard γ.2⟩,
        Subgroup.mem_subgroupOf.2 γ.2, rfl⟩
    exact h.aedisjoint (i := ⟨_, hmem γ₁⟩) (j := ⟨_, hmem γ₂⟩)
      (fun hcon => hne' (congrArg Subtype.val hcon))

/-- **H4.** The covolume of `Γ(2+i)` is a positive integer multiple of the volume of
the half box: the index of its image in the effective Picard group. Together with the
value of that volume — Humbert's formula, `G/3` — this would give the covolume in
closed form. -/

theorem exists_fundamentalDomain_gammaTwoI_eq_index_nsmul :
    ∃ F : Set H3, IsFundamentalDomain gammaTwoI F hvol ∧
      hvol F = gammaTwoIEff.index • hvol halfBox := by
  have hindex : gammaTwoIEff.index ≠ 0 := by rw [index_gammaTwoIEff]; norm_num
  refine ⟨⋃ q : PicardEff ⧸ gammaTwoIEff, (Quotient.out q)⁻¹ • halfBox, ?_, ?_⟩
  · exact isFundamentalDomain_of_eff
      (isFundamentalDomain_iUnion_out isFundamentalDomain_halfBox gammaTwoIEff)
  · exact measure_eq_index_smul gammaTwoIEff (Nat.pos_of_ne_zero hindex)
      isFundamentalDomain_halfBox
      (isFundamentalDomain_iUnion_out isFundamentalDomain_halfBox gammaTwoIEff)

theorem isOpen_halfBoxOpen : IsOpen halfBoxOpen := by
  have c0 : Continuous fun p : H3 => p.1 0 := (continuous_apply 0).comp continuous_subtype_val
  have c1 : Continuous fun p : H3 => p.1 1 := (continuous_apply 1).comp continuous_subtype_val
  have c2 : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have cN : Continuous fun p : H3 => N p.1 := by
    have h : (fun p : H3 => N p.1)
        = fun p : H3 => p.1 0 * p.1 0 + p.1 1 * p.1 1 + p.1 2 * p.1 2 := rfl
    rw [h]
    exact ((c0.mul c0).add (c1.mul c1)).add (c2.mul c2)
  have h : halfBoxOpen = ((fun p : H3 => |p.1 0|) ⁻¹' Iio (1 / 2)) ∩
      (((fun p : H3 => p.1 1) ⁻¹' Ioi 0) ∩ (((fun p : H3 => p.1 1) ⁻¹' Iio (1 / 2)) ∩
        ((fun p : H3 => N p.1) ⁻¹' Ioi 1))) := rfl
  rw [h]
  exact (isOpen_Iio.preimage c0.abs).inter ((isOpen_Ioi.preimage c1).inter
    ((isOpen_Iio.preimage c1).inter (isOpen_Ioi.preimage cN)))

/-- The half box has finite positive volume, so the covolume above is finite and
positive as well. -/
theorem hvol_halfBox_pos : 0 < hvol halfBox := by
  have hpt : (0 : ℝ) < ![(0 : ℝ), 1 / 4, 2] 2 := by
    norm_num [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  have hne : halfBoxOpen.Nonempty := by
    refine ⟨⟨![(0 : ℝ), 1 / 4, 2], hpt⟩, ?_, ?_, ?_, ?_⟩ <;>
      norm_num [N, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  refine lt_of_lt_of_le (hvol_pos_of_isOpen isOpen_halfBoxOpen hne) (measure_mono ?_)
  rintro p ⟨hx, hy0, hy1, hN⟩
  exact ⟨le_of_lt hx, le_of_lt hy0, le_of_lt hy1, le_of_lt hN⟩


/-- Catalan's constant. -/
noncomputable def catalan : ℝ := ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ)

/-- **Humbert's formula for `ℚ(i)`.** The volume of the half box is `G/3`. -/
theorem hvol_halfBox_eq_catalan : hvol halfBox = ENNReal.ofReal (catalan / 3) := by
  unfold catalan
  rw [hvol_halfBox_eq_ofReal_integral,
    CatalanLogSin.integral_log_one_sub_inv_four_cos_sq_eq_neg_catalan_div_three, neg_neg]

/-- Catalan's constant is positive, read off from the positivity of the volume. -/
theorem catalan_pos : 0 < catalan := by
  have h := hvol_halfBox_pos
  rw [hvol_halfBox_eq_catalan, ENNReal.ofReal_pos] at h
  linarith

/-- **The covolume of `Γ(2+i)` is `20 G`**: `60 · G/3`. -/
theorem exists_fundamentalDomain_gammaTwoI_eq_twenty_catalan :
    ∃ F : Set H3, IsFundamentalDomain gammaTwoI F hvol ∧
      hvol F = ENNReal.ofReal (20 * catalan) := by
  obtain ⟨F, hF, h⟩ := exists_fundamentalDomain_gammaTwoI_eq_index_nsmul
  refine ⟨F, hF, ?_⟩
  rw [h, index_gammaTwoIEff, hvol_halfBox_eq_catalan, nsmul_eq_mul,
    show (20 * catalan) = ((60 : ℕ) : ℝ) * (catalan / 3) by push_cast; ring,
    ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast]

end Final

end Thurston23

open MeasureTheory in
theorem solution :
    ∃ v ∈ Thurston23.hyperbolicVolumes, ∃ q : ℚ, 0 < q ∧
      v = (q : ℝ) * ∑' n : ℕ, (-1) ^ n / ((2 * n + 1) ^ 2 : ℝ) := by
  obtain ⟨F, hF, h⟩ := Thurston23.exists_fundamentalDomain_gammaTwoI_eq_twenty_catalan
  have hG := Thurston23.catalan_pos
  refine ⟨20 * Thurston23.catalan,
    ⟨↥Thurston23.gammaTwoI, inferInstance, inferInstance, Thurston23.isKleinian_gammaTwoI, F, hF,
      h, by positivity⟩, 20, by norm_num, ?_⟩
  unfold Thurston23.catalan
  push_cast
  ring
