-- Prove2me | solution 1 for Thurston23.exists_hyperbolicVolume_rat_mul_LChiMinusThree
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-14T16:34:02.265968+00:00
-- url     : https://prove2.me/submissions/8c9f6ae7-3d6d-402a-99c8-dba453da7c6c

import Mathlib
import Definitions.Def_Thurston23_bundle
import Definitions.Def_Thurston23_mobius
import Definitions.Def_Thurston23_eisenstein
import Theorems.Thm_Thurston23_isKleinian_gammaSeven
import Theorems.Thm_Thurston23_isFundamentalDomain_eisBox
import Theorems.Thm_Thurston23_hvol_eisBox_eq_ofReal_integral
import Theorems.Thm_EisensteinLogSin_integral_log_one_sub_inv_four_cos_sq_pi_div_six

/-!
A hyperbolic `3`-manifold whose volume is a rational multiple of `√3 L(2, χ₋₃)`: the manifold
`ℍ³/Γ(3 + ω)`, of volume `n · √3 L(2, χ₋₃)/8` for the index `n` of `Γ(3 + ω)` in the effective
Bianchi group. See the explanation for the reduction.
-/

noncomputable def EisensteinLogSin.lchi3 : ℝ :=
  ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))

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

instance : Countable EisInt :=
  (show Function.Injective (fun z : EisInt => (z.a, z.b)) from
    fun _ _ h => EisInt.ext (congrArg Prod.fst h) (congrArg Prod.snd h)).countable

instance : Countable SL(2, EisInt) :=
  (show Function.Injective (fun (g : SL(2, EisInt)) (i j : Fin 2) => g i j) from
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j).countable

instance : Countable eisGroup := by
  change Countable (Set.range (Matrix.SpecialLinearGroup.map EisInt.toComplex))
  exact (Set.countable_range _).to_subtype

instance : SMulInvariantMeasure EisEff H3 hvol :=
  ⟨fun q _ hs => (EisEff.measurePreserving q).measure_preimage hs.nullMeasurableSet⟩

instance : MeasurableConstSMul EisEff H3 :=
  ⟨fun q => (EisEff.measurePreserving q).measurable⟩

theorem gammaSeven_le_eisGroup : gammaSeven ≤ eisGroup := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem eisMap_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map EisInt.toComplex :
      SL(2, EisInt) →* SL(2, ℂ)) := fun g₁ g₂ h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => EisInt.toC_injective (by
    simpa using congrArg (fun g : SL(2, ℂ) => g i j) h)

/-- The congruence subgroup has finite index in the Bianchi group. -/
theorem relIndex_gammaSeven_eisGroup : gammaSeven.relIndex eisGroup ≠ 0 := by
  rw [gammaSeven, eisGroup, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ eisMap_injective, Subgroup.relIndex_top_right]
  show (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealP)).ker.index ≠ 0
  exact Subgroup.FiniteIndex.index_ne_zero

/-- An element of `Γ(3+ω)` acting trivially is the identity: the action is free. -/
theorem eq_one_of_mem_gammaSeven_of_smul_eq {g : SL(2, ℂ)} (hg : g ∈ gammaSeven)
    (h : ∀ p : H3, g • p = p) : g = 1 := by
  by_contra hne
  exact isKleinian_gammaSeven.free ⟨g, hg⟩ (fun h1 => hne (congrArg Subtype.val h1)) basepoint
    (h basepoint)

/-- `Γ(3+ω)` injects into the effective quotient. -/
theorem gammaSeven_toEff_injective :
    Function.Injective (fun γ : gammaSeven =>
      (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩ : EisEff)) := by
  intro γ₁ γ₂ h
  have hmem : (⟨(γ₁ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₁.2⟩ : eisGroup)⁻¹ *
      ⟨(γ₂ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₂.2⟩ ∈ eisKer := QuotientGroup.eq.mp h
  rw [eisKer, MonoidHom.mem_ker] at hmem
  have htriv : ∀ p : H3, ((γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ))) • p = p := by
    intro p
    have := congrArg (fun e : Equiv.Perm H3 => e p) hmem
    simpa using this
  have hmul : (γ₁ : SL(2, ℂ))⁻¹ * (γ₂ : SL(2, ℂ)) ∈ gammaSeven :=
    gammaSeven.mul_mem (gammaSeven.inv_mem γ₁.2) γ₂.2
  have hone := eq_one_of_mem_gammaSeven_of_smul_eq hmul htriv
  exact Subtype.ext (inv_mul_eq_one.1 hone)

/-- A fundamental domain for the image of `Γ(3+ω)` is one for `Γ(3+ω)` itself. -/
theorem isFundamentalDomain_of_eisEff {F : Set H3}
    (h : IsFundamentalDomain gammaSevenEff F hvol) : IsFundamentalDomain gammaSeven F hvol := by
  refine ⟨h.nullMeasurableSet, ?_, ?_⟩
  · filter_upwards [h.ae_covers] with x hx
    obtain ⟨q, hq⟩ := hx
    obtain ⟨g, hg, hgq⟩ := Subgroup.mem_map.1 q.2
    refine ⟨⟨(g : SL(2, ℂ)), Subgroup.mem_subgroupOf.1 hg⟩, ?_⟩
    have : ((g : eisGroup) : EisEff) = (q : EisEff) := hgq
    show (g : SL(2, ℂ)) • x ∈ F
    have hq' : (q : EisEff) • x ∈ F := hq
    rw [← this] at hq'
    exact hq'
  · intro γ₁ γ₂ hne
    have hinj := gammaSeven_toEff_injective
    have hne' : (QuotientGroup.mk ⟨(γ₁ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₁.2⟩ : EisEff) ≠
        QuotientGroup.mk ⟨(γ₂ : SL(2, ℂ)), gammaSeven_le_eisGroup γ₂.2⟩ := fun h' => hne (hinj h')
    have hmem : ∀ γ : gammaSeven,
        (QuotientGroup.mk ⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩ : EisEff) ∈
          gammaSevenEff := by
      intro γ
      exact Subgroup.mem_map.2 ⟨⟨(γ : SL(2, ℂ)), gammaSeven_le_eisGroup γ.2⟩,
        Subgroup.mem_subgroupOf.2 γ.2, rfl⟩
    exact h.aedisjoint (i := ⟨_, hmem γ₁⟩) (j := ⟨_, hmem γ₂⟩)
      (fun hcon => hne' (congrArg Subtype.val hcon))

/-- The covolume of `Γ(3+ω)` is a positive integer multiple of the volume of
the box: the index of its image in the effective Bianchi group. With the value of that volume,
`√3 L(2, χ₋₃)/8`, this is the covolume in closed form up to the index. -/
theorem exists_fundamentalDomain_gammaSeven_eq_nsmul :
    ∃ (n : ℕ) (F : Set H3), 0 < n ∧ IsFundamentalDomain gammaSeven F hvol ∧
      hvol F = n • hvol eisBox := by
  have hindex : gammaSevenEff.index ≠ 0 := by
    have hdvd : gammaSevenEff.index ∣ (gammaSeven.subgroupOf eisGroup).index :=
      Subgroup.index_map_dvd (gammaSeven.subgroupOf eisGroup) (QuotientGroup.mk'_surjective _)
    intro h
    rw [h] at hdvd
    exact relIndex_gammaSeven_eisGroup (zero_dvd_iff.1 hdvd)
  refine ⟨gammaSevenEff.index, ⋃ q : EisEff ⧸ gammaSevenEff, (Quotient.out q)⁻¹ • eisBox,
    Nat.pos_of_ne_zero hindex, ?_, ?_⟩
  · exact isFundamentalDomain_of_eisEff
      (isFundamentalDomain_iUnion_out isFundamentalDomain_eisBox gammaSevenEff)
  · exact measure_eq_index_smul gammaSevenEff (Nat.pos_of_ne_zero hindex)
      isFundamentalDomain_eisBox
      (isFundamentalDomain_iUnion_out isFundamentalDomain_eisBox gammaSevenEff)

theorem eisBase_of_open {w : ℂ} (h : eisBaseOpen w) : eisBase w :=
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

/-- **The volume of the box over the rhombus is `√3 L(2, χ₋₃)/8`**: Humbert's formula for
`ℚ(√-3)`, the covolume of `PSL(2, ℤ[ω])`. -/
theorem hvol_eisBox_eq :
    hvol eisBox = ENNReal.ofReal (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8) := by
  unfold EisensteinLogSin.lchi3
  rw [hvol_eisBox_eq_ofReal_integral,
    EisensteinLogSin.integral_log_one_sub_inv_four_cos_sq_pi_div_six, neg_neg]

theorem isOpen_eisBoxOpen : IsOpen eisBoxOpen := by
  have h0 : Continuous fun p : H3 => p.1 0 := (continuous_apply 0).comp continuous_subtype_val
  have h1 : Continuous fun p : H3 => p.1 1 := (continuous_apply 1).comp continuous_subtype_val
  have h2 : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have hv : Continuous fun p : H3 => p.1 0 + Real.sqrt 3 * p.1 1 := h0.add (continuous_const.mul h1)
  have hN : Continuous fun p : H3 => N p.1 := by
    unfold N
    exact ((h0.mul h0).add (h1.mul h1)).add (h2.mul h2)
  have hset : eisBoxOpen = {p : H3 | 0 < p.1 0} ∩ {p : H3 | p.1 0 < 1 / 2} ∩
      {p : H3 | 0 < p.1 0 + Real.sqrt 3 * p.1 1} ∩ {p : H3 | p.1 0 + Real.sqrt 3 * p.1 1 < 1} ∩
      {p : H3 | 1 < N p.1} := by
    ext p
    simp only [eisBoxOpen, eisBaseOpen, zc_re, zc_im, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset]
  exact ((((isOpen_lt continuous_const h0).inter (isOpen_lt h0 continuous_const)).inter
    (isOpen_lt continuous_const hv)).inter (isOpen_lt hv continuous_const)).inter
    (isOpen_lt continuous_const hN)

theorem hvol_eisBox_pos : 0 < hvol eisBox := by
  have hpt : 1 / 4 + Real.sqrt 3 * (1 / 10) < 1 := by
    have : Real.sqrt 3 < 2 := by
      rw [show (2:ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  have hs := sqrt3_pos
  have hmem : (⟨![1 / 4, 1 / 10, 2], by show (0:ℝ) < 2; norm_num⟩ : H3) ∈ eisBoxOpen := by
    refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · show (0:ℝ) < 1 / 4; norm_num
    · show (1:ℝ) / 4 < 1 / 2; norm_num
    · show (0:ℝ) < 1 / 4 + Real.sqrt 3 * (1 / 10); positivity
    · show (1:ℝ) / 4 + Real.sqrt 3 * (1 / 10) < 1; exact hpt
    · show (1:ℝ) < 1 / 4 * (1 / 4) + 1 / 10 * (1 / 10) + 2 * 2; norm_num
  refine lt_of_lt_of_le (hvol_pos_of_isOpen isOpen_eisBoxOpen ⟨_, hmem⟩) (measure_mono ?_)
  rintro p ⟨hb, hN⟩
  exact ⟨eisBase_of_open hb, hN.le⟩

theorem sqrt3_mul_lchi3_pos : 0 < Real.sqrt 3 * EisensteinLogSin.lchi3 / 8 := by
  have h := hvol_eisBox_pos
  rw [hvol_eisBox_eq, ENNReal.ofReal_pos] at h
  exact h

/-- **The covolume of `Γ(3 + ω)` is a positive integer multiple of `√3 L(2, χ₋₃)/8`.** -/
theorem exists_fundamentalDomain_gammaSeven_eq_lchi3 :
    ∃ (n : ℕ) (F : Set H3), 0 < n ∧ IsFundamentalDomain gammaSeven F hvol ∧
      hvol F = ENNReal.ofReal (n * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8)) := by
  obtain ⟨n, F, hn, hF, hvolF⟩ := exists_fundamentalDomain_gammaSeven_eq_nsmul
  refine ⟨n, F, hn, hF, ?_⟩
  rw [hvolF, hvol_eisBox_eq, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg n),
    ENNReal.ofReal_natCast]

end Final

end Thurston23

open MeasureTheory in
theorem solution :
    ∃ v ∈ Thurston23.hyperbolicVolumes, ∃ q : ℚ, 0 < q ∧
      v = (q : ℝ) * (Real.sqrt 3 *
        ∑' n : ℕ, (1 / ((3 * n + 1) ^ 2 : ℝ) - 1 / ((3 * n + 2) ^ 2 : ℝ))) := by
  obtain ⟨n, F, hn, hF, hvolF⟩ := Thurston23.exists_fundamentalDomain_gammaSeven_eq_lchi3
  have hpos : 0 < (n : ℝ) * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8) := by
    have := Thurston23.sqrt3_mul_lchi3_pos
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  refine ⟨(n : ℝ) * (Real.sqrt 3 * EisensteinLogSin.lchi3 / 8),
    ⟨↥Thurston23.gammaSeven, inferInstance, inferInstance, Thurston23.isKleinian_gammaSeven, F, hF,
      hvolF, hpos⟩, (n : ℚ) / 8, by positivity, ?_⟩
  unfold EisensteinLogSin.lchi3
  push_cast
  ring
