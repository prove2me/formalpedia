-- Prove2me | solution 1 for Thurston23.hyperbolicVolumes_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @t4v1
-- created : 2026-09-11T10:32:37.870882+00:00
-- url     : https://prove2.me/submissions/97863b86-9087-46e6-a047-32028f06f381

import Mathlib
import Definitions.Def_Thurston23_bundle

/-!
Milestone 2: the set of hyperbolic volumes is nonempty.

The witness is the congruence subgroup `Γ(2 + i)` of the Picard group
`SL(2, ℤ[i])`, acting on `H3` by Möbius transformations through the quaternions.
The action is by isometries of `hdist` and preserves `hvol`; the Picard group
acts properly discontinuously, and `Γ(2 + i)` has finite index in it and acts
freely, so `Γ(2 + i)` is Kleinian. A free, properly discontinuous action by
homeomorphisms has a measurable fundamental domain, of measure at most that of
any set meeting every orbit; reduction theory for the Picard group gives such a
set of finite volume, and `hvol ≠ 0` makes the volume positive.

Everything below the imports is taken verbatim from the mission's source file
`Thurston23.lean`, with the five bundle declarations removed (they come from
`Definitions.Def_Thurston23_bundle`) and the open goal theorems dropped.
-/

set_option autoImplicit false

namespace Thurston23

open MeasureTheory

/-! ## Supporting material for Milestone 1

Mathlib relates the measures of two fundamental domains of the *same* action but
has nothing relating a group to a finite-index subgroup, so that is developed
here. `measure_eq_index_smul` is the general measure-theoretic statement;
`countable_of_properlyDiscontinuous` supplies the countability of the acting
group that Mathlib's fundamental-domain API requires throughout, and which for a
Kleinian group is a consequence of proper discontinuity rather than a hypothesis.
-/

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

section Countability

/-- A group acting properly discontinuously on a nonempty σ-compact space is countable:
every element moves the basepoint inside some member of a countable compact covering,
and each such member admits only finitely many elements. -/
theorem countable_of_properlyDiscontinuous {Γ Y : Type*} [Group Γ] [TopologicalSpace Y]
    [MulAction Γ Y] [SigmaCompactSpace Y] (x₀ : Y)
    (hpd : ∀ K : Set Y, IsCompact K →
      {g : Γ | ((fun p : Y => g • p) '' K ∩ K).Nonempty}.Finite) :
    Countable Γ := by
  have hcov : ∀ y : Y, ∃ n, y ∈ compactCovering Y n := fun y =>
    Set.mem_iUnion.mp (by rw [iUnion_compactCovering]; trivial)
  have hsub : (Set.univ : Set Γ) ⊆ ⋃ n : ℕ,
      {g : Γ | ((fun p : Y => g • p) '' (compactCovering Y n) ∩ compactCovering Y n).Nonempty} := by
    intro g _
    obtain ⟨a, ha⟩ := hcov x₀
    obtain ⟨b, hb⟩ := hcov (g • x₀)
    refine Set.mem_iUnion.2 ⟨max a b, g • x₀, ⟨x₀, ?_, rfl⟩, ?_⟩
    · exact compactCovering_subset Y (le_max_left a b) ha
    · exact compactCovering_subset Y (le_max_right a b) hb
  exact Set.countable_univ_iff.mp
    (((Set.countable_iUnion fun n => (hpd _ (isCompact_compactCovering Y n)).countable)).mono hsub)

end Countability

section H3Topology

/-- The defining condition of `H3` is open, so `ℍ³` is an open subset of `ℝ³`. -/
theorem isOpen_upperHalfSpace : IsOpen {p : Fin 3 → ℝ | 0 < p 2} :=
  isOpen_lt continuous_const (continuous_apply 2)

instance : LocallyCompactSpace H3 := isOpen_upperHalfSpace.locallyCompactSpace

/-- A basepoint of `ℍ³`, used to witness countability of a Kleinian group. -/
def basepoint : H3 := ⟨fun _ => 1, by norm_num⟩

end H3Topology

/-! ## A sanity check on `hvol`

`hvol` is built with `Measure.comap`, which returns the zero measure when its
measurability side conditions fail — silently, with every theorem about it
still type-checking. Nothing else in the bundle evaluates `hvol` on a concrete
set, so one value is computed here: the unit cusp box `[0,1]² × [1,∞)` has
hyperbolic volume `∫₀¹∫₀¹∫₁^∞ t⁻³ = 1/2`. Consequently `hvol ≠ 0`. -/

section CuspBox

open Set

set_option maxHeartbeats 400000

/-- The unit cusp box `[0,1] × [0,1] × [1,∞)`, as a subset of `ℝ³`. -/
def cuspBox : Set (Fin 3 → ℝ) := Set.pi Set.univ ![Icc 0 1, Icc 0 1, Ici 1]

/-- The hyperbolic volume of the unit cusp box is `∫₀¹∫₀¹∫₁^∞ t⁻³ = 1/2`. -/
theorem hvol_cusp_box : hvol (Subtype.val ⁻¹' cuspBox) = 2⁻¹ := by
  set S : Fin 3 → Set ℝ := ![Icc 0 1, Icc 0 1, Ici 1] with hS
  set h : Fin 3 → ℝ → ℝ := ![fun _ => 1, fun _ => 1, fun t => (t ^ 3)⁻¹] with hh
  set f : Fin 3 → ℝ → ℝ := fun i => (S i).indicator (h i) with hf
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i; fin_cases i
    · exact measurableSet_Icc
    · exact measurableSet_Icc
    · exact measurableSet_Ici
  have hBm : MeasurableSet cuspBox := MeasurableSet.univ_pi hSm
  have hemb : MeasurableEmbedding (Subtype.val : H3 → Fin 3 → ℝ) :=
    MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const (measurable_pi_apply 2))
  have hBsub : cuspBox ⊆ Set.range (Subtype.val : H3 → Fin 3 → ℝ) := by
    intro x hx
    have h2 : x 2 ∈ Ici (1 : ℝ) := Set.mem_univ_pi.1 hx 2
    exact ⟨⟨x, lt_of_lt_of_le one_pos h2⟩, rfl⟩
  set F : (Fin 3 → ℝ) → ENNReal := fun x => ENNReal.ofReal ((x 2 ^ (3 : ℕ))⁻¹) with hF
  have hFm : Measurable F := ((measurable_pi_apply 2).pow_const 3).inv.ennreal_ofReal
  -- Step 1: unfold `hvol` and transport the integral from `H3` to `ℝ³`.
  have step1 : hvol (Subtype.val ⁻¹' cuspBox) = ∫⁻ x in cuspBox, F x := by
    show ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
      (fun p : H3 => F p.1) (Subtype.val ⁻¹' cuspBox) = _
    rw [withDensity_apply _ (hemb.measurable hBm), ← lintegral_indicator (hemb.measurable hBm),
      ← lintegral_indicator hBm]
    calc ∫⁻ p, (Subtype.val ⁻¹' cuspBox).indicator (fun p : H3 => F p.1) p
            ∂(volume.comap Subtype.val)
        = ∫⁻ p, cuspBox.indicator F (Subtype.val p) ∂(volume.comap Subtype.val) :=
          lintegral_congr fun p => rfl
      _ = ∫⁻ x, cuspBox.indicator F x ∂((volume.comap Subtype.val).map Subtype.val) :=
          (lintegral_map (hFm.indicator hBm) hemb.measurable).symm
      _ = ∫⁻ x, cuspBox.indicator F x ∂(volume.restrict (Set.range Subtype.val)) := by
          rw [hemb.map_comap]
      _ = ∫⁻ x, cuspBox.indicator F x := by
          rw [lintegral_indicator hBm, lintegral_indicator hBm, Measure.restrict_restrict hBm,
            Set.inter_eq_left.2 hBsub]
  -- Step 2: the integrand is a product of one-variable functions.
  have hpt : ∀ x, cuspBox.indicator F x = ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    by_cases hx : x ∈ cuspBox
    · have hxi : ∀ i, x i ∈ S i := Set.mem_univ_pi.1 hx
      rw [Set.indicator_of_mem hx, Fin.prod_univ_three]
      simp only [hf, Set.indicator_of_mem (hxi 0), Set.indicator_of_mem (hxi 1),
        Set.indicator_of_mem (hxi 2), hh]
      simp [hF]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ S i := by
        by_contra hcon
        push_neg at hcon
        exact hx (Set.mem_univ_pi.2 hcon)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hf, Set.indicator_of_notMem hi])]
      simp
  -- Step 3: each factor is integrable and nonnegative.
  have hfi : ∀ i, Integrable (f i) := by
    intro i; fin_cases i
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · show Integrable ((Ici (1 : ℝ)).indicator fun t => (t ^ 3)⁻¹)
      refine (integrable_indicator_iff measurableSet_Ici).2 ?_
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num) one_pos).congr_fun
        (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) ≤ t := (lt_trans zero_lt_one ht).le
      simp [Real.rpow_neg ht0]
  have hint : Integrable (fun x : Fin 3 → ℝ => ∏ i, f i (x i)) := Integrable.fintype_prod hfi
  have hnn : 0 ≤ᵐ[(volume : Measure (Fin 3 → ℝ))] fun x => ∏ i, f i (x i) := by
    refine Filter.Eventually.of_forall fun x => Finset.prod_nonneg fun i _ =>
      Set.indicator_nonneg (fun t ht => ?_) _
    fin_cases i
    · exact zero_le_one
    · exact zero_le_one
    · have ht1 : (1 : ℝ) ≤ t := ht
      show (0 : ℝ) ≤ (t ^ 3)⁻¹
      positivity
  -- Step 4: Fubini, then three one-dimensional integrals.
  have I0 : ∫ t, f 0 t = 1 := by
    show ∫ t, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 1
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le zero_le_one]
    simp
  have I1 : ∫ t, f 1 t = 1 := by
    show ∫ t, (Icc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ)) t = 1
    rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le zero_le_one]
    simp
  have I2 : ∫ t, f 2 t = 1 / 2 := by
    show ∫ t, (Ici (1 : ℝ)).indicator (fun t => (t ^ 3)⁻¹) t = 1 / 2
    have hcongr : ∫ t in Ioi (1 : ℝ), (t ^ 3)⁻¹ = ∫ t in Ioi (1 : ℝ), t ^ (-3 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        have ht0 : (0 : ℝ) ≤ t := (lt_trans zero_lt_one ht).le
        simp [Real.rpow_neg ht0]
    rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hcongr,
      integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  rw [step1, ← lintegral_indicator hBm]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_fintype_prod_volume_eq_prod,
    Fin.prod_univ_three, I0, I1, I2, one_mul, one_mul, one_div,
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

/-- Consequently the hyperbolic volume is neither the zero measure nor identically infinite. -/
theorem hvol_ne_zero : hvol ≠ 0 := by
  intro h
  have := hvol_cusp_box
  rw [h] at this
  simp at this
  exact (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top) this.symm

end CuspBox

/-! ## Milestones -/

/-- **Milestone 1.** Passing to a subgroup of index `n` multiplies the volume
by `n`: a fundamental domain for `H` is the union of `n` translates of a
fundamental domain for `G`. This is the source of every known rational relation
between the volumes of hyperbolic `3`-manifolds — commensurable manifolds, that
is manifolds with a common finite cover, have rationally related volumes — and
it is what makes the literal reading of Question 23 false. Stated in `ℝ≥0∞` so
that no degenerate case is hidden by `ENNReal.ofReal`. -/
theorem volume_of_finite_index {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (H : Subgroup G) (hH : 0 < H.index)
    (F FH : Set H3) (hF : MeasureTheory.IsFundamentalDomain G F hvol)
    (hFH : MeasureTheory.IsFundamentalDomain H FH hvol) :
    hvol FH = H.index • hvol F := by
  haveI : SMulInvariantMeasure G H3 hvol :=
    ⟨fun g _ hs => (hG.measure_preserving g).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul G H3 := ⟨fun g => (hG.measure_preserving g).measurable⟩
  haveI : Countable G :=
    countable_of_properlyDiscontinuous basepoint hG.properly_discontinuous
  exact measure_eq_index_smul H hH hF hFH

/-! ## Commensurable groups have rationally related volumes

The positive half of Thurston's framing, stated exactly. If `Γ₁` and `Γ₂` are
subgroups of one Kleinian group and are commensurable — Mathlib's definition is
that `Γ₁ ⊓ Γ₂` has finite index in both — then Milestone 1 applied twice to the
same fundamental domain for the intersection gives
`[Γ₁ : Γ₁ ⊓ Γ₂] · vol Γ₁ = vol (Γ₁ ⊓ Γ₂) = [Γ₂ : Γ₁ ⊓ Γ₂] · vol Γ₂`, so the ratio of
the volumes is rational. Every known rational relation between volumes of
hyperbolic `3`-manifolds arises this way. The converse is false: Ruberman's
mutation preserves volume and typically destroys commensurability.

The general statement is proved for any countable group acting on any measure
space with an invariant measure, as Milestone 1 was, and then specialised. -/

section Commensurable

open Pointwise

variable {Γ X : Type*} [Group Γ] [MulAction Γ X] [MeasurableSpace X] {μ : Measure X}

/-- A subgroup's action preserves whatever the ambient action preserves. -/
instance instSMulInvariantMeasureSubgroup (S : Subgroup Γ) [SMulInvariantMeasure Γ X μ] :
    SMulInvariantMeasure S X μ :=
  ⟨fun c _ hs => SMulInvariantMeasure.measure_preimage_smul (c : Γ) hs⟩

/-- A subgroup's action is measurable whenever the ambient action is. -/
instance instMeasurableConstSMulSubgroup (S : Subgroup Γ) [MeasurableConstSMul Γ X] :
    MeasurableConstSMul S X :=
  ⟨fun c => measurable_const_smul (c : Γ)⟩

/-- `Γ₁ ⊓ Γ₂` viewed inside `Γ₁` is the same group as viewed inside `Γ₂`: swap the two
membership proofs. Built by hand so that everything about it is `rfl`. -/
def subgroupOfSwap (Γ₁ Γ₂ : Subgroup Γ) : ↥(Γ₂.subgroupOf Γ₁) ≃ ↥(Γ₁.subgroupOf Γ₂) where
  toFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  invFun x := ⟨⟨x.1.1, x.2⟩, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Commensurable subgroups have rationally related covolumes**, in the form free of
rationals and of finiteness hypotheses: the two relative indices weight the two
volumes equally, both being the volume of a fundamental domain for `Γ₁ ⊓ Γ₂`. -/
theorem relIndex_smul_measure_eq [Countable Γ] [SMulInvariantMeasure Γ X μ]
    [MeasurableConstSMul Γ X] {Γ₁ Γ₂ : Subgroup Γ} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set X} (hF₁ : IsFundamentalDomain Γ₁ F₁ μ) (hF₂ : IsFundamentalDomain Γ₂ F₂ μ) :
    Γ₂.relIndex Γ₁ • μ F₁ = Γ₁.relIndex Γ₂ • μ F₂ := by
  -- one fundamental domain for the intersection, built inside `Γ₂` ...
  have hH₂ : IsFundamentalDomain (Γ₁.subgroupOf Γ₂)
      (⋃ q : Γ₂ ⧸ Γ₁.subgroupOf Γ₂, (Quotient.out q)⁻¹ • F₂) μ :=
    isFundamentalDomain_iUnion_out hF₂ _
  -- ... is also one inside `Γ₁`, since both act through `Γ`
  have hH₁ : IsFundamentalDomain (Γ₂.subgroupOf Γ₁)
      (⋃ q : Γ₂ ⧸ Γ₁.subgroupOf Γ₂, (Quotient.out q)⁻¹ • F₂) μ := by
    have := hH₂.image_of_equiv (Equiv.refl X) (Measure.QuasiMeasurePreserving.id μ)
      (subgroupOfSwap Γ₁ Γ₂) (fun g x => rfl)
    simpa using this
  have e₂ := measure_eq_index_smul (Γ₁.subgroupOf Γ₂)
    (Nat.pos_of_ne_zero h.1) hF₂ hH₂
  have e₁ := measure_eq_index_smul (Γ₂.subgroupOf Γ₁)
    (Nat.pos_of_ne_zero h.2) hF₁ hH₁
  show (Γ₂.subgroupOf Γ₁).index • μ F₁ = (Γ₁.subgroupOf Γ₂).index • μ F₂
  rw [← e₁, ← e₂]

/-- The same, as a rational multiple. -/
theorem exists_rat_measure_eq [Countable Γ] [SMulInvariantMeasure Γ X μ]
    [MeasurableConstSMul Γ X] {Γ₁ Γ₂ : Subgroup Γ} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set X} (hF₁ : IsFundamentalDomain Γ₁ F₁ μ) (hF₂ : IsFundamentalDomain Γ₂ F₂ μ) :
    ∃ q : ℚ, 0 < q ∧ μ F₁ = ENNReal.ofReal q * μ F₂ := by
  have key := relIndex_smul_measure_eq h hF₁ hF₂
  have h₁ : 0 < Γ₂.relIndex Γ₁ := Nat.pos_of_ne_zero h.2
  have h₂ : 0 < Γ₁.relIndex Γ₂ := Nat.pos_of_ne_zero h.1
  set n₁ := Γ₂.relIndex Γ₁
  set n₂ := Γ₁.relIndex Γ₂
  refine ⟨(n₂ : ℚ) / n₁, div_pos (by exact_mod_cast h₂) (by exact_mod_cast h₁), ?_⟩
  rw [nsmul_eq_mul, nsmul_eq_mul] at key
  have hn₁ : (n₁ : ENNReal) ≠ 0 := by exact_mod_cast h₁.ne'
  have hn₁' : (n₁ : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top n₁
  calc μ F₁ = (n₁ : ENNReal)⁻¹ * (n₁ * μ F₁) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hn₁ hn₁', one_mul]
    _ = (n₁ : ENNReal)⁻¹ * (n₂ * μ F₂) := by rw [key]
    _ = ENNReal.ofReal (((n₂ : ℚ) / n₁ : ℚ) : ℝ) * μ F₂ := by
        rw [← mul_assoc]
        congr 1
        rw [Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
          ENNReal.ofReal_div_of_pos (by exact_mod_cast h₁), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]

end Commensurable

/-- A subgroup of a Kleinian group is Kleinian: all four conditions restrict. -/
theorem IsKleinian.subgroup {G : Type} [Group G] [MulAction G H3] (hG : IsKleinian G)
    (Γ : Subgroup G) : IsKleinian Γ where
  isometry g p q := hG.isometry (g : G) p q
  measure_preserving g := hG.measure_preserving (g : G)
  free g hg p := hG.free (g : G) (fun h => hg (Subtype.ext h)) p
  properly_discontinuous K hK := by
    show (Subtype.val ⁻¹' {g : G | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}).Finite
    exact (hG.properly_discontinuous K hK).preimage Subtype.coe_injective.injOn

/-- The volume of a subgroup's quotient is a hyperbolic volume. -/
theorem mem_hyperbolicVolumes_of_subgroup {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (Γ : Subgroup G) {F : Set H3} (hF : IsFundamentalDomain Γ F hvol)
    {v : ℝ} (hv : hvol F = ENNReal.ofReal v) (hpos : 0 < v) : v ∈ hyperbolicVolumes :=
  ⟨Γ, inferInstance, inferInstance, hG.subgroup Γ, F, hF, hv, hpos⟩

/-- **Commensurable Kleinian groups have rationally related volumes.** For subgroups
`Γ₁, Γ₂` of one Kleinian group with a common finite-index subgroup, the volumes of
their quotients have rational ratio. This is the source of every known rational
relation in `hyperbolicVolumes`; Thurston's question is whether it is the only one. -/
theorem hvol_ratio_rational_of_commensurable {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) {Γ₁ Γ₂ : Subgroup G} (h : Subgroup.Commensurable Γ₁ Γ₂)
    {F₁ F₂ : Set H3} (hF₁ : IsFundamentalDomain Γ₁ F₁ hvol)
    (hF₂ : IsFundamentalDomain Γ₂ F₂ hvol) {v₁ v₂ : ℝ}
    (hv₁ : hvol F₁ = ENNReal.ofReal v₁) (hv₂ : hvol F₂ = ENNReal.ofReal v₂)
    (h₁ : 0 < v₁) (h₂ : 0 < v₂) : ∃ q : ℚ, v₁ = q * v₂ := by
  haveI : SMulInvariantMeasure G H3 hvol :=
    ⟨fun g _ hs => (hG.measure_preserving g).measure_preimage hs.nullMeasurableSet⟩
  haveI : MeasurableConstSMul G H3 := ⟨fun g => (hG.measure_preserving g).measurable⟩
  haveI : Countable G :=
    countable_of_properlyDiscontinuous basepoint hG.properly_discontinuous
  obtain ⟨q, hq, hqv⟩ := exists_rat_measure_eq h hF₁ hF₂
  refine ⟨q, ?_⟩
  rw [hv₁, hv₂, ← ENNReal.ofReal_mul (by positivity)] at hqv
  exact (ENNReal.ofReal_eq_ofReal_iff h₁.le (by positivity)).1 hqv

/-! ## Toward Milestone 2: the Möbius action of `SL(2, ℂ)`

Milestone 2 needs a lattice, and every lattice comes from `PSL(2, ℂ)`. This section
gives `ℍ³` its action by `SL(2, ℂ)`: the point `(x, y, t)` is the quaternion
`x + y i + t j`, and `g = !![a, b; c, d]` acts by `q ↦ (a q + b)(c q + d)⁻¹`. Nothing
here is hyperbolic geometry yet — isometry and volume preservation are the next
sub-problems — but the action is what everything after it is stated about. -/

section Mobius

open MatrixGroups Quaternion

/-- Mathlib's `Star ℍ[R]` instance is stated with the `Zero`, `One`, `Neg` arguments of
`Quaternion R` derived from `[CommRing R]`, while `ℍ` elaborates them directly; instance
search cannot unify the two while the ring instance is still a metavariable, so `star`
fails to elaborate on `ℍ` in a fresh file. This is Mathlib's instance, restated. -/
instance instStarH : Star ℍ := Quaternion.instStar

/-! The point `(x, y, t)` of the upper half-space is the quaternion `x + y i + t j`, and
`g = !![a, b; c, d]` acts by `q ↦ (a q + b)(c q + d)⁻¹`, with the complex entries
embedded in the quaternions. The image has `k`-part `t · Im(det g)` and `j`-part
`t · Re(det g)` before normalising, so `det g = 1` is exactly what keeps the action
inside the half-space. The composition law is division-ring algebra: the complex
entries sit to the left of `q` and commute among themselves. -/

/-- The point `(x, y, t)` as the quaternion `x + y i + t j`. -/
def toQ (p : H3) : ℍ := ⟨p.1 0, p.1 1, p.1 2, 0⟩

theorem toQ_imK (p : H3) : (toQ p).imK = 0 := rfl

theorem toQ_imJ_pos (p : H3) : 0 < (toQ p).imJ := p.2

theorem toQ_injective : Function.Injective toQ := by
  intro p q h
  apply Subtype.ext
  funext i
  fin_cases i
  · exact congrArg QuaternionAlgebra.re h
  · exact congrArg QuaternionAlgebra.imI h
  · exact congrArg QuaternionAlgebra.imJ h

/-- The Möbius transformation `q ↦ (a q + b)(c q + d)⁻¹` on the quaternions. -/
noncomputable def mobiusQ (g : SL(2, ℂ)) (q : ℍ) : ℍ :=
  (((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) * ((((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))⁻¹)

theorem sl2_det (g : SL(2, ℂ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have := Matrix.SpecialLinearGroup.det_coe (A := g)
  rwa [Matrix.det_fin_two] at this

theorem sl2_row_ne_zero (g : SL(2, ℂ)) : g 1 0 ≠ 0 ∨ g 1 1 ≠ 0 := by
  by_contra h
  push_neg at h
  have hdet := sl2_det g
  rw [h.1, h.2] at hdet
  simp at hdet

theorem normSq_pos {a : ℍ} (ha : a ≠ 0) : 0 < normSq a :=
  lt_of_le_of_ne normSq_nonneg (Ne.symm (normSq_ne_zero.2 ha))

/-- On the half-space the denominator never vanishes: its `j` and `k` parts are
`c.re · t` and `c.im · t`. -/
theorem denom_ne_zero {c d : ℂ} (hcd : c ≠ 0 ∨ d ≠ 0) {q : ℍ} (hK : q.imK = 0)
    (hJ : 0 < q.imJ) : (c : ℍ) * q + (d : ℍ) ≠ 0 := by
  intro h
  by_cases hc : c = 0
  · subst hc
    have hd : d ≠ 0 := hcd.resolve_left (by simp)
    apply hd
    have hre := congrArg QuaternionAlgebra.re h
    have him := congrArg QuaternionAlgebra.imI h
    simp at hre him
    exact Complex.ext hre him
  · apply hc
    have hJ' : ((c : ℍ) * q + (d : ℍ)).imJ = 0 := by rw [h]; rfl
    have hK' : ((c : ℍ) * q + (d : ℍ)).imK = 0 := by rw [h]; rfl
    simp [hK, hJ.ne'] at hJ' hK'
    exact Complex.ext hJ' hK'

/-- The key computation: numerator times conjugate denominator has `j`-part `t` and
`k`-part `0`. This is where `det g = 1` enters. -/
theorem num_mul_star_denom (g : SL(2, ℂ)) {q : ℍ} (hK : q.imK = 0) :
    ((((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) *
        star (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))).imJ = q.imJ ∧
    ((((g 0 0 : ℂ) : ℍ) * q + ((g 0 1 : ℂ) : ℍ)) *
        star (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ))).imK = 0 := by
  have hdet := sl2_det g
  have hre := congrArg Complex.re hdet
  have him := congrArg Complex.im hdet
  simp at hre him
  constructor
  · simp [hK]
    linear_combination q.imJ * hre
  · simp [hK]
    linear_combination q.imJ * him

/-- The Möbius transformation preserves the half-space, scaling `t` by `1 / |c q + d|²`. -/
theorem mobiusQ_imJ (g : SL(2, ℂ)) {q : ℍ} (hK : q.imK = 0) :
    (mobiusQ g q).imJ = q.imJ / normSq (((g 1 0 : ℂ) : ℍ) * q + ((g 1 1 : ℂ) : ℍ)) ∧
    (mobiusQ g q).imK = 0 := by
  obtain ⟨h1, h2⟩ := num_mul_star_denom g hK
  unfold mobiusQ
  rw [Quaternion.inv_def, Algebra.mul_smul_comm]
  constructor
  · rw [Quaternion.imJ_smul, h1, smul_eq_mul, div_eq_inv_mul]
  · rw [Quaternion.imK_smul, h2, smul_zero]

/-- The Möbius action of `SL(2, ℂ)` on the upper half-space model. -/
noncomputable instance instSMulSL2C : SMul SL(2, ℂ) H3 where
  smul g p := ⟨![(mobiusQ g (toQ p)).re, (mobiusQ g (toQ p)).imI, (mobiusQ g (toQ p)).imJ], by
    show 0 < (mobiusQ g (toQ p)).imJ
    rw [(mobiusQ_imJ g (toQ_imK p)).1]
    exact div_pos p.2 (normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2))⟩

theorem mobius_smul_def (g : SL(2, ℂ)) (p : H3) : (g • p).1 =
    ![(mobiusQ g (toQ p)).re, (mobiusQ g (toQ p)).imI, (mobiusQ g (toQ p)).imJ] := rfl

theorem toQ_smul (g : SL(2, ℂ)) (p : H3) : toQ (g • p) = mobiusQ g (toQ p) := by
  have h2 := (mobiusQ_imJ g (toQ_imK p)).2
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · exact h2.symm

/-- Composition of linear fractional maps, in any division ring, with the coefficients on
the left. Only the inner denominator needs to be nonzero. -/
theorem lf_comp {K : Type*} [DivisionRing K] (a₁ b₁ c₁ d₁ N M : K) (hM : M ≠ 0) :
    (a₁ * (N * M⁻¹) + b₁) * (c₁ * (N * M⁻¹) + d₁)⁻¹ =
      (a₁ * N + b₁ * M) * (c₁ * N + d₁ * M)⁻¹ := by
  have e1 : a₁ * (N * M⁻¹) + b₁ = (a₁ * N + b₁ * M) * M⁻¹ := by
    rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hM, mul_one]
  have e2 : c₁ * (N * M⁻¹) + d₁ = (c₁ * N + d₁ * M) * M⁻¹ := by
    rw [add_mul, mul_assoc, mul_assoc, mul_inv_cancel₀ hM, mul_one]
  rw [e1, e2, mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc M⁻¹, inv_mul_cancel₀ hM, one_mul]

theorem mobiusQ_mul (g₁ g₂ : SL(2, ℂ)) {q : ℍ}
    (hM : ((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ) ≠ 0) :
    mobiusQ g₁ (mobiusQ g₂ q) = mobiusQ (g₁ * g₂) q := by
  unfold mobiusQ
  rw [lf_comp _ _ _ _ _ _ hM]
  have hn : ((g₁ 0 0 : ℂ) : ℍ) * (((g₂ 0 0 : ℂ) : ℍ) * q + ((g₂ 0 1 : ℂ) : ℍ)) +
      ((g₁ 0 1 : ℂ) : ℍ) * (((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ)) =
      (((g₁ * g₂) 0 0 : ℂ) : ℍ) * q + (((g₁ * g₂) 0 1 : ℂ) : ℍ) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coeComplex_add, coeComplex_mul]
    noncomm_ring
  have hd : ((g₁ 1 0 : ℂ) : ℍ) * (((g₂ 0 0 : ℂ) : ℍ) * q + ((g₂ 0 1 : ℂ) : ℍ)) +
      ((g₁ 1 1 : ℂ) : ℍ) * (((g₂ 1 0 : ℂ) : ℍ) * q + ((g₂ 1 1 : ℂ) : ℍ)) =
      (((g₁ * g₂) 1 0 : ℂ) : ℍ) * q + (((g₁ * g₂) 1 1 : ℂ) : ℍ) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      coeComplex_add, coeComplex_mul]
    noncomm_ring
  rw [hn, hd]

noncomputable instance instMulActionSL2C : MulAction SL(2, ℂ) H3 where
  one_smul p := toQ_injective (by
    rw [toQ_smul]
    unfold mobiusQ
    simp [Matrix.SpecialLinearGroup.coe_one])
  mul_smul g₁ g₂ p := toQ_injective (by
    rw [toQ_smul, toQ_smul, toQ_smul]
    exact (mobiusQ_mul g₁ g₂ (denom_ne_zero (sl2_row_ne_zero g₂) (toQ_imK p) p.2)).symm)

end Mobius

/-! ## Toward Milestone 2: the action is by isometries

`hdist` is `arcosh` of `1 + |p − q|² / (2 p₃ q₃)`. Under `g` the height `p₃` is divided by
`D_p = |c p + d|²`, and the squared distance `|p − q|²` is divided by `D_p D_q`, so the
quotient is unchanged. The second fact is the two-sided factorisation
`(p c + d)(g p − g q)(c q + d) = p − q` in the quaternions — `c` to the right of `p` on the
left factor — which needs only that the complex entries commute among themselves and
that `ad − bc = 1`; taking norms, nothing is ever inverted. -/

section Isometry

open MatrixGroups Quaternion

/-- The argument of `arcosh` in `hdist`. -/
noncomputable def coshDist (p q : H3) : ℝ :=
  1 + (∑ i, (p.1 i - q.1 i) ^ 2) / (2 * p.1 2 * q.1 2)

theorem hdist_eq_log_coshDist (p q : H3) :
    hdist p q = Real.log (coshDist p q + Real.sqrt (coshDist p q ^ 2 - 1)) := rfl

theorem sum_sq_sub_eq_normSq (p q : H3) :
    ∑ i, (p.1 i - q.1 i) ^ 2 = normSq (toQ p - toQ q) := by
  rw [normSq_def', Fin.sum_univ_three]
  simp [toQ]

/-- `P c + d` and `c P + d` differ only in the sign of the `k`-part when `P.imK = 0`. -/
theorem normSq_mul_coe_add (c d : ℂ) {P : ℍ} (hK : P.imK = 0) :
    normSq (P * (c : ℍ) + (d : ℍ)) = normSq ((c : ℍ) * P + (d : ℍ)) := by
  simp [normSq_def', hK]
  ring

/-- The two-sided factorisation behind the invariance of the distance. -/
theorem mobius_sub_factor (g : SL(2, ℂ)) {P Q : ℍ}
    (hMP : ((g 1 0 : ℂ) : ℍ) * P + ((g 1 1 : ℂ) : ℍ) ≠ 0)
    (hMQ : ((g 1 0 : ℂ) : ℍ) * Q + ((g 1 1 : ℂ) : ℍ) ≠ 0) :
    (P * ((g 1 0 : ℂ) : ℍ) + ((g 1 1 : ℂ) : ℍ)) * (mobiusQ g P - mobiusQ g Q) *
        (((g 1 0 : ℂ) : ℍ) * Q + ((g 1 1 : ℂ) : ℍ)) = P - Q := by
  unfold mobiusQ
  set A : ℍ := ((g 0 0 : ℂ) : ℍ) with hA
  set B : ℍ := ((g 0 1 : ℂ) : ℍ) with hB
  set C : ℍ := ((g 1 0 : ℂ) : ℍ) with hC
  set D : ℍ := ((g 1 1 : ℂ) : ℍ) with hD
  have comm : ∀ x y : ℂ, (x : ℍ) * (y : ℍ) = (y : ℍ) * (x : ℍ) := fun x y => by
    rw [← coeComplex_mul, ← coeComplex_mul, mul_comm]
  have hCA : C * A = A * C := comm _ _
  have hCB : C * B = B * C := comm _ _
  have hDB : D * B = B * D := comm _ _
  have hDA' : D * A = A * D := comm _ _
  have hAD : A * D = 1 + B * C := by
    have h := sl2_det g
    rw [sub_eq_iff_eq_add] at h
    have h' := congrArg (fun z : ℂ => (z : ℍ)) h
    simp only [coeComplex_add, coeComplex_mul, coeComplex_one] at h'
    rw [hA, hD, hB, hC, h', add_comm]
  have hDA : D * A = 1 + B * C := by rw [hDA', hAD]
  have e1 : (P * C + D) * (A * P + B) = (P * A + B) * (C * P + D) := by
    calc (P * C + D) * (A * P + B)
        = P * (C * A) * P + P * (C * B) + (D * A) * P + D * B := by noncomm_ring
      _ = P * (A * C) * P + P * (B * C) + (1 + B * C) * P + B * D := by
          rw [hCA, hCB, hDA, hDB]
      _ = P * (A * C) * P + P * (1 + B * C) + (B * C) * P + B * D := by noncomm_ring
      _ = P * (A * C) * P + P * (A * D) + (B * C) * P + B * D := by rw [hAD]
      _ = (P * A + B) * (C * P + D) := by noncomm_ring
  have e2 : (P * A + B) * (C * Q + D) - (P * C + D) * (A * Q + B) = P - Q := by
    calc (P * A + B) * (C * Q + D) - (P * C + D) * (A * Q + B)
        = P * (A * C) * Q + P * (A * D) + (B * C) * Q + B * D
            - (P * (C * A) * Q + P * (C * B) + (D * A) * Q + D * B) := by noncomm_ring
      _ = P * (A * C) * Q + P * (1 + B * C) + (B * C) * Q + B * D
            - (P * (A * C) * Q + P * (B * C) + (1 + B * C) * Q + B * D) := by
          rw [hAD, hCA, hCB, hDA, hDB]
      _ = P - Q := by noncomm_ring
  calc (P * C + D) * ((A * P + B) * (C * P + D)⁻¹ - (A * Q + B) * (C * Q + D)⁻¹) * (C * Q + D)
      = ((P * C + D) * (A * P + B)) * (C * P + D)⁻¹ * (C * Q + D)
          - (P * C + D) * (A * Q + B) * ((C * Q + D)⁻¹ * (C * Q + D)) := by noncomm_ring
    _ = (P * A + B) * (C * P + D) * (C * P + D)⁻¹ * (C * Q + D)
          - (P * C + D) * (A * Q + B) * 1 := by rw [e1, inv_mul_cancel₀ hMQ]
    _ = (P * A + B) * (C * Q + D) - (P * C + D) * (A * Q + B) := by
          rw [mul_inv_cancel_right₀ hMP, mul_one]
    _ = P - Q := e2

/-- `|g P − g Q|² = |P − Q|² / (|c P + d|² · |c Q + d|²)`. -/
theorem normSq_mobius_sub (g : SL(2, ℂ)) {P Q : ℍ} (hKP : P.imK = 0) (hKQ : Q.imK = 0)
    (hJP : 0 < P.imJ) (hJQ : 0 < Q.imJ) :
    normSq (mobiusQ g P - mobiusQ g Q) =
      normSq (P - Q) / (normSq (((g 1 0 : ℂ) : ℍ) * P + ((g 1 1 : ℂ) : ℍ)) *
        normSq (((g 1 0 : ℂ) : ℍ) * Q + ((g 1 1 : ℂ) : ℍ))) := by
  have hMP := denom_ne_zero (sl2_row_ne_zero g) hKP hJP
  have hMQ := denom_ne_zero (sl2_row_ne_zero g) hKQ hJQ
  have key := congrArg normSq (mobius_sub_factor g hMP hMQ)
  rw [map_mul, map_mul, normSq_mul_coe_add _ _ hKP] at key
  rw [eq_div_iff (mul_ne_zero (normSq_ne_zero.2 hMP) (normSq_ne_zero.2 hMQ)), ← key]
  ring

theorem coshDist_smul (g : SL(2, ℂ)) (p q : H3) : coshDist (g • p) (g • q) = coshDist p q := by
  unfold coshDist
  rw [sum_sq_sub_eq_normSq, sum_sq_sub_eq_normSq, toQ_smul, toQ_smul]
  rw [show (g • p).1 2 = (mobiusQ g (toQ p)).imJ from rfl,
    show (g • q).1 2 = (mobiusQ g (toQ q)).imJ from rfl,
    (mobiusQ_imJ g (toQ_imK p)).1, (mobiusQ_imJ g (toQ_imK q)).1,
    normSq_mobius_sub g (toQ_imK p) (toQ_imK q) p.2 q.2,
    show (toQ p).imJ = p.1 2 from rfl, show (toQ q).imJ = q.1 2 from rfl]
  have h1 := (normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)).ne'
  have h2 := (normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK q) q.2)).ne'
  have hp : p.1 2 ≠ 0 := p.2.ne'
  have hq : q.1 2 ≠ 0 := q.2.ne'
  field_simp

/-- **M2.2.** The Möbius action of `SL(2, ℂ)` is by isometries of `hdist`. -/
theorem hdist_smul (g : SL(2, ℂ)) (p q : H3) : hdist (g • p) (g • q) = hdist p q := by
  rw [hdist_eq_log_coshDist, hdist_eq_log_coshDist, coshDist_smul]

end Isometry

/-! ## Toward Milestone 2: the action preserves the volume

`hvol` is Lebesgue measure with density `ρ(x) = t⁻³` on the half-space `U ⊆ ℝ³`. A map
`Φ : ℝ³ → ℝ³` that is differentiable and injective on `U` transports `hvol` to itself
exactly when `|det Φ'(x)| · ρ(Φ x) = ρ(x)` on `U`; that is Mathlib's change of variables
formula. `SL(2, ℂ)` is generated by three families with explicit coordinate formulas —
translations `T b`, the linear maps `D a`, and the inversion `S` — and measure
preservation composes, so each family is handled once and the rest is the Bruhat
factorisation `g = T(a/c) · S · D(c) · T(d/c)`. Preimages under `g` are images under
`g⁻¹`, so only images are ever computed. -/

section Volume

open MatrixGroups Quaternion Pointwise

/-- The density of `hvol`, as a function on `ℝ³`. -/
noncomputable def ρ (x : Fin 3 → ℝ) : ENNReal := ENNReal.ofReal ((x 2 ^ (3 : ℕ))⁻¹)

theorem measurable_ρ : Measurable ρ := ((measurable_pi_apply 2).pow_const 3).inv.ennreal_ofReal

theorem measurableEmbedding_val : MeasurableEmbedding (Subtype.val : H3 → Fin 3 → ℝ) :=
  MeasurableEmbedding.subtype_coe (measurableSet_lt measurable_const (measurable_pi_apply 2))

/-- `hvol` is `volume.withDensity ρ`, transported to the half-space. -/
theorem hvol_apply {s : Set H3} (hs : MeasurableSet s) :
    hvol s = ∫⁻ x in Subtype.val '' s, ρ x := by
  have hemb := measurableEmbedding_val
  have hB : MeasurableSet (Subtype.val '' s) := hemb.measurableSet_image.2 hs
  have hBsub : Subtype.val '' s ⊆ Set.range (Subtype.val : H3 → Fin 3 → ℝ) :=
    Set.image_subset_range _ _
  show ((volume : Measure (Fin 3 → ℝ)).comap Subtype.val).withDensity
    (fun p : H3 => ρ p.1) s = _
  rw [withDensity_apply _ hs, ← lintegral_indicator hs, ← lintegral_indicator hB]
  calc ∫⁻ p, s.indicator (fun p : H3 => ρ p.1) p ∂(volume.comap Subtype.val)
      = ∫⁻ p, (Subtype.val '' s).indicator ρ (Subtype.val p) ∂(volume.comap Subtype.val) := by
        refine lintegral_congr fun p => ?_
        by_cases hp : p ∈ s
        · simp [Set.indicator, hp, Subtype.val_injective.mem_set_image]
        · simp [Set.indicator, hp, Subtype.val_injective.mem_set_image]
    _ = ∫⁻ x, (Subtype.val '' s).indicator ρ x ∂((volume.comap Subtype.val).map Subtype.val) :=
        (lintegral_map (measurable_ρ.indicator hB) hemb.measurable).symm
    _ = ∫⁻ x, (Subtype.val '' s).indicator ρ x ∂(volume.restrict (Set.range Subtype.val)) := by
        rw [hemb.map_comap]
    _ = ∫⁻ x, (Subtype.val '' s).indicator ρ x := by
        rw [lintegral_indicator hB, lintegral_indicator hB, Measure.restrict_restrict hB,
          Set.inter_eq_left.2 hBsub]

/-- Preimages under `g` are images under `g⁻¹`: if `g⁻¹` maps every measurable set to one of
the same volume, then `g` preserves `hvol`. -/
theorem measurePreserving_smul_of_image (g : SL(2, ℂ)) (hmeas : Measurable fun p : H3 => g • p)
    (himg : ∀ s : Set H3, MeasurableSet s → hvol ((fun p => g⁻¹ • p) '' s) = hvol s) :
    MeasurePreserving (fun p : H3 => g • p) hvol hvol := by
  refine ⟨hmeas, ?_⟩
  ext s hs
  rw [Measure.map_apply hmeas hs, Set.preimage_smul, ← himg s hs]
  rfl

theorem continuous_toQ : Continuous toQ := by
  have h : toQ = fun p : H3 =>
      Quaternion.linearIsometryEquivTuple.symm (WithLp.toLp 2 ![p.1 0, p.1 1, p.1 2, 0]) := by
    funext p
    simp [toQ]
  rw [h]
  refine Quaternion.linearIsometryEquivTuple.symm.continuous.comp
    ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 4 => ℝ)).comp (continuous_pi fun i => ?_))
  fin_cases i
  · show Continuous fun p : H3 => p.1 0
    exact (continuous_apply 0).comp continuous_subtype_val
  · show Continuous fun p : H3 => p.1 1
    exact (continuous_apply 1).comp continuous_subtype_val
  · show Continuous fun p : H3 => p.1 2
    exact (continuous_apply 2).comp continuous_subtype_val
  · show Continuous fun _ : H3 => (0 : ℝ)
    exact continuous_const

theorem continuous_mobius_toQ (g : SL(2, ℂ)) : Continuous fun p : H3 => mobiusQ g (toQ p) := by
  have hden : ∀ p : H3, ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) ≠ 0 := fun p =>
    denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2
  unfold mobiusQ
  exact ((continuous_const.mul continuous_toQ).add continuous_const).mul
    (((continuous_const.mul continuous_toQ).add continuous_const).inv₀ hden)

theorem continuous_smul (g : SL(2, ℂ)) : Continuous fun p : H3 => g • p := by
  rw [continuous_induced_rng]
  show Continuous fun p : H3 =>
    ![(mobiusQ g (toQ p)).re, (mobiusQ g (toQ p)).imI, (mobiusQ g (toQ p)).imJ]
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact continuous_re.comp (continuous_mobius_toQ g)
  · exact continuous_imI.comp (continuous_mobius_toQ g)
  · exact continuous_imJ.comp (continuous_mobius_toQ g)

/-- The action of `g` as a homeomorphism of `ℍ³`. -/
noncomputable def smulHomeomorph (g : SL(2, ℂ)) : H3 ≃ₜ H3 :=
  { MulAction.toPerm g with
    continuous_toFun := continuous_smul g
    continuous_invFun := continuous_smul g⁻¹ }

/-- Change of variables for `volume.withDensity ρ` on subsets of the half-space. -/
theorem lintegral_ρ_image (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Φ' : (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)))
    (hΦ : ∀ x, 0 < x 2 → HasFDerivAt Φ (Φ' x) x)
    (hinj : Set.InjOn Φ {x | 0 < x 2})
    (hdet : ∀ x, 0 < x 2 → ENNReal.ofReal |(Φ' x).det| * ρ (Φ x) = ρ x)
    {s : Set (Fin 3 → ℝ)} (hs : MeasurableSet s) (hsU : s ⊆ {x | 0 < x 2}) :
    ∫⁻ x in Φ '' s, ρ x = ∫⁻ x in s, ρ x := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun x hx => (hΦ x (hsU hx)).hasFDerivWithinAt) (hinj.mono hsU)]
  exact setLIntegral_congr_fun hs (fun x hx => hdet x (hsU hx))

/-- If the action of `g` is a change of variables with the right Jacobian, it maps every
measurable set to one of the same volume. -/
theorem hvol_image_smul (g : SL(2, ℂ)) (Φ : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (Φ' : (Fin 3 → ℝ) → ((Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ)))
    (hΦ : ∀ x, 0 < x 2 → HasFDerivAt Φ (Φ' x) x)
    (hdet : ∀ x, 0 < x 2 → ENNReal.ofReal |(Φ' x).det| * ρ (Φ x) = ρ x)
    (hcomp : ∀ p : H3, (g • p).1 = Φ p.1)
    {s : Set H3} (hs : MeasurableSet s) : hvol ((fun p => g • p) '' s) = hvol s := by
  -- injectivity of `Φ` on the half-space is injectivity of the action
  have hinj : Set.InjOn Φ {x | 0 < x 2} := by
    intro x hx y hy hxy
    have h : g • (⟨x, hx⟩ : H3) = g • ⟨y, hy⟩ :=
      Subtype.ext (by rw [hcomp ⟨x, hx⟩, hcomp ⟨y, hy⟩]; exact hxy)
    exact congrArg Subtype.val (MulAction.injective g h)
  have hs' : MeasurableSet ((fun p => g • p) '' s) :=
    (smulHomeomorph g).measurableEmbedding.measurableSet_image.2 hs
  rw [hvol_apply hs', hvol_apply hs]
  have himg : Subtype.val '' ((fun p => g • p) '' s) = Φ '' (Subtype.val '' s) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun p _ => hcomp p
  rw [himg]
  exact lintegral_ρ_image Φ Φ' hΦ hinj hdet (measurableEmbedding_val.measurableSet_image.2 hs)
    (fun x ⟨p, _, hp⟩ => hp ▸ p.2)

/-! ### Translations -/

/-- `!![1, b; 0, 1]`, acting by `q ↦ q + b`. -/
def T (b : ℂ) : SL(2, ℂ) := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem T_mul_T (b c : ℂ) : T b * T c = T (b + c) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem T_zero : T 0 = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [T]

theorem T_inv (b : ℂ) : (T b)⁻¹ = T (-b) :=
  inv_eq_of_mul_eq_one_right (by rw [T_mul_T, add_neg_cancel, T_zero])

theorem T_smul_val (b : ℂ) (p : H3) : (T b • p).1 = p.1 + ![b.re, b.im, 0] := by
  rw [mobius_smul_def]
  have h : mobiusQ (T b) (toQ p) = toQ p + (b : ℍ) := by
    simp [mobiusQ, T]
  rw [h]
  ext i
  fin_cases i <;> simp [toQ]

theorem measurePreserving_T (b : ℂ) : MeasurePreserving (fun p : H3 => T b • p) hvol hvol := by
  refine measurePreserving_smul_of_image _ (continuous_smul _).measurable fun s hs => ?_
  rw [T_inv]
  refine hvol_image_smul (T (-b)) (fun x => x + ![(-b).re, (-b).im, 0])
    (fun _ => ContinuousLinearMap.id ℝ _) (fun x _ => (hasFDerivAt_id x).add_const _)
    (fun x _ => ?_) (T_smul_val (-b)) hs
  simp [ρ, ContinuousLinearMap.det]

/-! ### The linear maps `D a` -/

theorem coe_inv_inv (a : ℂ) : (((a⁻¹ : ℂ) : ℍ))⁻¹ = (a : ℍ) := by
  have h : ((a⁻¹ : ℂ) : ℍ) = (a : ℍ)⁻¹ := by
    rw [← Quaternion.coe_ofComplex]
    exact map_inv₀ Quaternion.ofComplex a
  rw [h, inv_inv]

/-- `!![a, 0; 0, a⁻¹]`, acting by `q ↦ a q a`, i.e. `z ↦ a² z`, `t ↦ |a|² t`. -/
noncomputable def D (a : ℂ) (ha : a ≠ 0) : SL(2, ℂ) := ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

/-- The matrix of the linear map `D a` on `ℝ³`. -/
def Dmat (a : ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![a.re ^ 2 - a.im ^ 2, -(2 * a.re * a.im), 0;
     2 * a.re * a.im, a.re ^ 2 - a.im ^ 2, 0;
     0, 0, a.re ^ 2 + a.im ^ 2]

theorem Dmat_det (a : ℂ) : (Dmat a).det = (a.re ^ 2 + a.im ^ 2) ^ 3 := by
  rw [Matrix.det_fin_three]
  simp [Dmat]
  ring

theorem D_mul_D (a b : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) : D a ha * D b hb = D (a * b) (mul_ne_zero ha hb) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [D, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem D_eq_one {c : ℂ} (hc : c ≠ 0) (h1 : c = 1) : D c hc = 1 := by
  subst h1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [D]

theorem D_inv (a : ℂ) (ha : a ≠ 0) : (D a ha)⁻¹ = D a⁻¹ (inv_ne_zero ha) :=
  inv_eq_of_mul_eq_one_right (by rw [D_mul_D]; exact D_eq_one _ (mul_inv_cancel₀ ha))

theorem D_smul_val (a : ℂ) (ha : a ≠ 0) (p : H3) :
    (D a ha • p).1 = Matrix.toLin' (Dmat a) p.1 := by
  rw [mobius_smul_def]
  have h : mobiusQ (D a ha) (toQ p) = (a : ℍ) * toQ p * (a : ℍ) := by
    simp [mobiusQ, D, coe_inv_inv]
  rw [h]
  ext i
  fin_cases i <;> simp [toQ, Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three] <;> ring

theorem measurePreserving_D (a : ℂ) (ha : a ≠ 0) :
    MeasurePreserving (fun p : H3 => D a ha • p) hvol hvol := by
  refine measurePreserving_smul_of_image _ (continuous_smul _).measurable fun s hs => ?_
  rw [D_inv]
  set b := a⁻¹ with hb
  have hb0 : b ≠ 0 := inv_ne_zero ha
  have hpos : 0 < b.re ^ 2 + b.im ^ 2 := by
    have := Complex.normSq_pos.2 hb0
    rw [Complex.normSq_apply] at this
    nlinarith [this]
  refine hvol_image_smul (D b hb0) (fun x => Matrix.toLin' (Dmat b) x)
    (fun _ => LinearMap.toContinuousLinearMap (Matrix.toLin' (Dmat b)))
    (fun x _ => (LinearMap.toContinuousLinearMap (Matrix.toLin' (Dmat b))).hasFDerivAt)
    (fun x hx => ?_) (D_smul_val b hb0) hs
  have hdet : (LinearMap.toContinuousLinearMap (Matrix.toLin' (Dmat b))).det =
      (b.re ^ 2 + b.im ^ 2) ^ 3 := by
    rw [ContinuousLinearMap.det, LinearMap.coe_toContinuousLinearMap, LinearMap.det_toLin',
      Dmat_det]
  have h2 : (Matrix.toLin' (Dmat b) x) 2 = (b.re ^ 2 + b.im ^ 2) * x 2 := by
    simp [Dmat, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [hdet, abs_of_pos (by positivity)]
  unfold ρ
  simp only [h2]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hx' : x 2 ≠ 0 := hx.ne'
  field_simp

/-! ### The inversion `S` -/

/-- `!![0, -1; 1, 0]`, acting by `q ↦ -q⁻¹`. -/
def S : SL(2, ℂ) := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

/-- `!![0, 1; -1, 0] = S⁻¹`, acting by the same map `q ↦ -q⁻¹`. -/
def S' : SL(2, ℂ) := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

theorem S_inv : S⁻¹ = S' := by
  refine inv_eq_of_mul_eq_one_right ?_
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [S, S', Matrix.mul_apply, Fin.sum_univ_two]

/-- The squared Euclidean norm on `ℝ³`. -/
def N (x : Fin 3 → ℝ) : ℝ := x 0 * x 0 + x 1 * x 1 + x 2 * x 2

theorem N_pos {x : Fin 3 → ℝ} (hx : 0 < x 2) : 0 < N x := by
  unfold N
  nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1), mul_pos hx hx]

/-- The inversion `x ↦ (-x₀, x₁, x₂) / |x|²` in coordinates. -/
noncomputable def invMap (x : Fin 3 → ℝ) : Fin 3 → ℝ := (N x)⁻¹ • ![-(x 0), x 1, x 2]

/-- The Jacobian matrix of `invMap`. -/
noncomputable def invJac (x : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-(N x)⁻¹ + 2 * x 0 * x 0 / N x ^ 2, 2 * x 0 * x 1 / N x ^ 2, 2 * x 0 * x 2 / N x ^ 2;
     -(2 * x 1 * x 0 / N x ^ 2), (N x)⁻¹ - 2 * x 1 * x 1 / N x ^ 2, -(2 * x 1 * x 2 / N x ^ 2);
     -(2 * x 2 * x 0 / N x ^ 2), -(2 * x 2 * x 1 / N x ^ 2), (N x)⁻¹ - 2 * x 2 * x 2 / N x ^ 2]

theorem invJac_det {x : Fin 3 → ℝ} (hx : 0 < x 2) : (invJac x).det = (N x ^ 3)⁻¹ := by
  have hN := (N_pos hx).ne'
  rw [Matrix.det_fin_three]
  simp only [invJac, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  field_simp
  unfold N
  ring

theorem coe_neg_one : ((-1 : ℂ) : ℍ) = -1 := by
  have h := map_neg Quaternion.ofComplex (1 : ℂ)
  rw [map_one, Quaternion.coe_ofComplex] at h
  exact h

theorem S'_smul_val (p : H3) : (S' • p).1 = invMap p.1 := by
  rw [mobius_smul_def]
  have h : mobiusQ S' (toQ p) = -(toQ p)⁻¹ := by
    simp [mobiusQ, S', coe_neg_one]
  have hN : normSq (toQ p) = N p.1 := by
    rw [normSq_def']; simp [toQ, N]; ring
  rw [h, Quaternion.inv_def, hN]
  ext i
  fin_cases i <;> simp [toQ, invMap]

/-- The derivative of `invMap`, built from projections so that its matrix is `invJac`. -/
noncomputable def invDeriv (x : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun i => ∑ j, invJac x i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j

theorem invDeriv_apply (x h : Fin 3 → ℝ) (i : Fin 3) :
    invDeriv x h i = ∑ j, invJac x i j * h j := by
  simp [invDeriv]

theorem toMatrix'_invDeriv (x : Fin 3 → ℝ) :
    LinearMap.toMatrix' (invDeriv x : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) = invJac x := by
  ext i j
  simp [LinearMap.toMatrix'_apply, invDeriv, Pi.single_apply]

theorem invDeriv_det {x : Fin 3 → ℝ} (hx : 0 < x 2) : (invDeriv x).det = (N x ^ 3)⁻¹ := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', toMatrix'_invDeriv, invJac_det hx]

set_option maxHeartbeats 1000000 in
theorem hasFDerivAt_invMap {x : Fin 3 → ℝ} (hx : 0 < x 2) :
    HasFDerivAt invMap (invDeriv x) x := by
  have hN0 : N x ≠ 0 := (N_pos hx).ne'
  have hsq : ∀ i : Fin 3, HasFDerivAt (fun y : Fin 3 → ℝ => y i * y i)
      (x i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i + x i • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) i) x := fun i => by
    have h := HasFDerivAt.mul (𝕜 := ℝ) (hasFDerivAt_apply (𝕜 := ℝ) i x)
      (hasFDerivAt_apply (𝕜 := ℝ) i x)
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by simp)
  have hN : HasFDerivAt N
      (x 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 + x 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0 +
        (x 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1 + x 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1) +
        (x 2 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2 + x 2 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2)) x :=
    ((hsq 0).add (hsq 1)).add (hsq 2)
  have hNi := (hasFDerivAt_inv (𝕜 := ℝ) hN0).comp x hN
  have key : ∀ i : Fin 3, HasFDerivAt (fun y => invMap y i)
      (∑ j, invJac x i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j) x := by
    intro i
    fin_cases i
    · refine ((hNi.mul ((hasFDerivAt_apply (𝕜 := ℝ) 0 x).neg)).congr_fderiv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [invMap])
      ext h
      simp [invJac, Fin.sum_univ_three]
      field_simp
      ring
    · refine ((hNi.mul (hasFDerivAt_apply (𝕜 := ℝ) 1 x)).congr_fderiv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [invMap])
      ext h
      simp [invJac, Fin.sum_univ_three]
      field_simp
      ring
    · refine ((hNi.mul (hasFDerivAt_apply (𝕜 := ℝ) 2 x)).congr_fderiv ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [invMap])
      ext h
      simp [invJac, Fin.sum_univ_three]
      field_simp
      ring
  exact (hasFDerivAt_pi (φ := fun i (y : Fin 3 → ℝ) => invMap y i)
    (φ' := fun i => ∑ j, invJac x i j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) j)).2 key

theorem measurePreserving_S : MeasurePreserving (fun p : H3 => S • p) hvol hvol := by
  refine measurePreserving_smul_of_image _ (continuous_smul _).measurable fun s hs => ?_
  rw [S_inv]
  refine hvol_image_smul S' invMap invDeriv (fun x hx => hasFDerivAt_invMap hx)
    (fun x hx => ?_) S'_smul_val hs
  have hN := N_pos hx
  have h2 : invMap x 2 = (N x)⁻¹ * x 2 := by simp [invMap]
  rw [invDeriv_det hx, abs_of_pos (by positivity)]
  unfold ρ
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hx' : x 2 ≠ 0 := hx.ne'
  have hN' := hN.ne'
  field_simp

/-! ### Every element, by the Bruhat factorisation -/

/-- For `c ≠ 0`, `g = T(a/c) · S · D(c) · T(d/c)`. -/
theorem sl2_eq_of_ne_zero (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) :
    g = T (g 0 0 / g 1 0) * S * D (g 1 0) hc * T (g 1 1 / g 1 0) := by
  have hdet := sl2_det g
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [T, S, D, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    linear_combination (-1) * hdet

/-- For `c = 0`, `g = D(a) · T(b/a)`. -/
theorem sl2_eq_of_eq_zero (g : SL(2, ℂ)) (hc : g 1 0 = 0) (ha : g 0 0 ≠ 0) :
    g = D (g 0 0) ha * T (g 0 1 / g 0 0) := by
  have hdet := sl2_det g
  have hd : g 1 1 = (g 0 0)⁻¹ := by
    rw [hc, mul_zero, sub_zero] at hdet
    exact eq_inv_of_mul_eq_one_right hdet
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [T, D, Matrix.mul_apply, Fin.sum_univ_two, hc, hd] <;>
    field_simp

/-- **M2.3.** The Möbius action of `SL(2, ℂ)` preserves the hyperbolic volume. -/
theorem measurePreserving_smul (g : SL(2, ℂ)) :
    MeasurePreserving (fun p : H3 => g • p) hvol hvol := by
  by_cases hc : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro ha
      have := sl2_det g
      rw [ha, hc] at this
      simp at this
    have key : (fun p : H3 => g • p) =
        (fun p => D (g 0 0) ha • p) ∘ (fun p => T (g 0 1 / g 0 0) • p) := by
      funext p
      conv_lhs => rw [sl2_eq_of_eq_zero g hc ha]
      simp [mul_smul]
    rw [key]
    exact (measurePreserving_D _ ha).comp (measurePreserving_T _)
  · have key : (fun p : H3 => g • p) =
        (fun p => T (g 0 0 / g 1 0) • p) ∘ (fun p => S • p) ∘ (fun p => D (g 1 0) hc • p) ∘
          (fun p => T (g 1 1 / g 1 0) • p) := by
      funext p
      conv_lhs => rw [sl2_eq_of_ne_zero g hc]
      simp [mul_smul]
    rw [key]
    exact (measurePreserving_T _).comp
      (measurePreserving_S.comp ((measurePreserving_D _ hc).comp (measurePreserving_T _)))

end Volume

/-! ## Toward Milestone 2: the Picard group acts properly discontinuously

The Picard group `SL(2, ℤ[i])` sits in `SL(2, ℂ)` as the matrices with Gaussian integer
entries. A compact subset of `ℍ³` lies in a box: heights in `[t₀, T]` with `t₀ > 0`, and
`|q|² ≤ R`. If `g` moves a point `q` of the box to a point of the box, the heights give
`|c q + d|² = t / t' ≤ T / t₀`; since `|c q + d|² ≥ |c|² t²` this bounds `c`, and then `d`.
The same argument for `g⁻¹ = !![d, -b; -c, a]`, which moves `g q` back to `q`, bounds `a`,
and `b = (g q)(c q + d) − a q` is bounded by the rest. Only finitely many Gaussian integers
lie in a disc. -/

section Picard

open MatrixGroups Quaternion

/-- The Picard group `SL(2, ℤ[i])`, as the subgroup of `SL(2, ℂ)` of matrices with Gaussian
integer entries (`mem_picard_iff`). -/
noncomputable def picard : Subgroup SL(2, ℂ) :=
  (Matrix.SpecialLinearGroup.map GaussianInt.toComplex).range

theorem entry_mem_of_mem_picard {g : SL(2, ℂ)} (hg : g ∈ picard) (i j : Fin 2) :
    ∃ z : GaussianInt, (z : ℂ) = g i j := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, by simp⟩

theorem mem_picard_iff {g : SL(2, ℂ)} :
    g ∈ picard ↔ ∀ i j, ∃ z : GaussianInt, (z : ℂ) = g i j := by
  refine ⟨entry_mem_of_mem_picard, fun hg => ?_⟩
  choose h hh using hg
  have hdet : (Matrix.of h).det = 1 := by
    apply GaussianInt.toComplex_injective
    rw [RingHom.map_det, map_one]
    convert g.2 using 2
    ext i j
    simp [hh]
  exact ⟨⟨Matrix.of h, hdet⟩, Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp [hh]⟩

theorem normSq_coeComplex (z : ℂ) : normSq (z : ℍ) = Complex.normSq z := by
  simp only [normSq_def', re_coeComplex, imI_coeComplex, imJ_coeComplex, imK_coeComplex,
    Complex.normSq_apply]
  ring

/-- `|x + y|² ≤ 2 (|x|² + |y|²)` in the quaternions. -/
theorem normSq_add_le (x y : ℍ) : normSq (x + y) ≤ 2 * (normSq x + normSq y) := by
  simp only [normSq_def', Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
    Quaternion.imK_add]
  nlinarith [sq_nonneg (x.re - y.re), sq_nonneg (x.imI - y.imI), sq_nonneg (x.imJ - y.imJ),
    sq_nonneg (x.imK - y.imK)]

/-- On the half-space `|c q + d|² ≥ |c|² t²`: the `j` and `k` parts of `c q + d` are `c t`. -/
theorem normSq_mul_imJ_le (c d : ℂ) {q : ℍ} (hK : q.imK = 0) :
    Complex.normSq c * q.imJ ^ 2 ≤ normSq ((c : ℍ) * q + (d : ℍ)) := by
  simp [normSq_def', hK, Complex.normSq_apply]
  nlinarith [sq_nonneg (c.re * q.re - c.im * q.imI + d.re),
    sq_nonneg (c.re * q.imI + c.im * q.re + d.im)]

/-- A compact subset of `ℍ³` lies in a box: heights in `[t₀, T]` with `t₀ > 0`, and
`|q|² ≤ R`. -/
theorem exists_box_of_isCompact {K : Set H3} (hK : IsCompact K) :
    ∃ t₀ T R : ℝ, 0 < t₀ ∧ ∀ p ∈ K, t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, 0, 0, one_pos, by simp⟩
  have hh : Continuous fun p : H3 => p.1 2 := (continuous_apply 2).comp continuous_subtype_val
  have hn : Continuous fun p : H3 => normSq (toQ p) := by
    have : (fun p : H3 => normSq (toQ p)) = fun p => ‖toQ p‖ * ‖toQ p‖ :=
      funext fun p => normSq_eq_norm_mul_self _
    rw [this]
    exact (continuous_norm.comp continuous_toQ).mul (continuous_norm.comp continuous_toQ)
  obtain ⟨p₀, -, hmin⟩ := hK.exists_isMinOn hne hh.continuousOn
  obtain ⟨T, hT⟩ := hK.bddAbove_image hh.continuousOn
  obtain ⟨R, hR⟩ := hK.bddAbove_image hn.continuousOn
  exact ⟨p₀.1 2, T, R, p₀.2, fun p hp => ⟨hmin hp, hT ⟨p, hp, rfl⟩, hR ⟨p, hp, rfl⟩⟩⟩

/-- The height of `g • p` is the height of `p` divided by `|c q + d|²`. -/
theorem smul_height (g : SL(2, ℂ)) (p : H3) :
    (g • p).1 2 = p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) :=
  (mobiusQ_imJ g (toQ_imK p)).1

/-- If `g` moves a point of the box to a point of the box, then `|c q + d|² ≤ T / t₀`, so
`|c|² ≤ T / t₀³` and `|d|² ≤ 2 (T / t₀ + R T / t₀³)`. -/
theorem bottom_row_bound (g : SL(2, ℂ)) {t₀ T R : ℝ} (ht₀ : 0 < t₀) {p : H3}
    (hp : t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R)
    (hgp : t₀ ≤ (g • p).1 2 ∧ (g • p).1 2 ≤ T ∧ normSq (toQ (g • p)) ≤ R) :
    normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤ T / t₀ ∧
      Complex.normSq (g 1 0) ≤ T / t₀ / t₀ ^ 2 ∧
      Complex.normSq (g 1 1) ≤ 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) := by
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc ⊢
  have hM0 : normSq M ≠ 0 := hMpos.ne'
  -- the denominator
  have hD : normSq M ≤ T / t₀ := by
    rw [le_div_iff₀ ht₀]
    have e : normSq M * (g • p).1 2 = p.1 2 := by rw [hh]; field_simp
    linarith [mul_le_mul_of_nonneg_left hgp.1 hMpos.le, hp.2.1]
  -- the entry `c`
  have ht2 : t₀ ^ 2 ≤ p.1 2 ^ 2 := by nlinarith [mul_le_mul hp.1 hp.1 ht₀.le (ht₀.le.trans hp.1)]
  have hcb : Complex.normSq (g 1 0) ≤ T / t₀ / t₀ ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith [mul_le_mul_of_nonneg_left ht2 (Complex.normSq_nonneg (g 1 0))]
  -- the entry `d = (c q + d) − c q`
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ T / t₀ / t₀ ^ 2 * R :=
    mul_le_mul hcb hp.2.2 normSq_nonneg ((Complex.normSq_nonneg _).trans hcb)
  exact ⟨hD, hcb, by linarith⟩

/-- The bound on every entry produced by `entries_bound`. -/
noncomputable def entryBound (t₀ T R : ℝ) : ℝ :=
  max (T / t₀ / t₀ ^ 2) (max (2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R))
    (2 * (R * (T / t₀) + 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R)))

/-- If `g` moves a point of the box to a point of the box, every entry of `g` is bounded in
terms of the box alone. -/
theorem entries_bound (g : SL(2, ℂ)) {t₀ T R : ℝ} (ht₀ : 0 < t₀) {p : H3}
    (hp : t₀ ≤ p.1 2 ∧ p.1 2 ≤ T ∧ normSq (toQ p) ≤ R)
    (hgp : t₀ ≤ (g • p).1 2 ∧ (g • p).1 2 ≤ T ∧ normSq (toQ (g • p)) ≤ R) :
    ∀ i j, Complex.normSq (g i j) ≤ entryBound t₀ T R := by
  obtain ⟨hD, hc, hd⟩ := bottom_row_bound g ht₀ hp hgp
  -- `g⁻¹ = !![d, -b; -c, a]` moves `g • p` back to `p`, so its bottom row bounds `a`
  have hinv := bottom_row_bound g⁻¹ ht₀ hgp (by rw [inv_smul_smul]; exact hp)
  have h11 : (g⁻¹) 1 1 = g 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  have ha := hinv.2.2
  rw [h11] at ha
  -- `b = (g q)(c q + d) − a q`
  have hM0 := denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2
  have hid : ((g 0 1 : ℂ) : ℍ) =
      toQ (g • p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) +
        -(((g 0 0 : ℂ) : ℍ) * toQ p) := by
    rw [toQ_smul]
    unfold mobiusQ
    rw [inv_mul_cancel_right₀ hM0]
    abel
  have hbb := normSq_add_le (toQ (g • p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)))
    (-(((g 0 0 : ℂ) : ℍ) * toQ p))
  rw [← hid, normSq_neg, map_mul, map_mul, normSq_coeComplex, normSq_coeComplex] at hbb
  have hR : 0 ≤ R := normSq_nonneg.trans hp.2.2
  have h1 : normSq (toQ (g • p)) * normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) ≤
      R * (T / t₀) := mul_le_mul hgp.2.2 hD normSq_nonneg hR
  have h2 : Complex.normSq (g 0 0) * normSq (toQ p) ≤
      2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R :=
    mul_le_mul ha hp.2.2 normSq_nonneg ((Complex.normSq_nonneg _).trans ha)
  have hb : Complex.normSq (g 0 1) ≤ 2 * (R * (T / t₀) + 2 * (T / t₀ + T / t₀ / t₀ ^ 2 * R) * R) := by
    linarith
  unfold entryBound
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
  · exact le_max_of_le_right (le_max_of_le_left ha)
  · exact le_max_of_le_right (le_max_of_le_right hb)
  · exact le_max_of_le_left hc
  · exact le_max_of_le_right (le_max_of_le_left hd)

/-- Only finitely many Gaussian integers lie in a disc. -/
theorem finite_gaussianInt_normSq_le (M : ℝ) :
    {w : ℂ | (∃ z : GaussianInt, (z : ℂ) = w) ∧ Complex.normSq w ≤ M}.Finite := by
  have key : ∀ k : ℤ, (k : ℝ) ^ 2 ≤ M → k ∈ Set.Icc (-⌈1 + M⌉) ⌈1 + M⌉ := by
    intro k hk
    have hc := Int.le_ceil (1 + M)
    have h1 : (k : ℝ) ≤ ⌈1 + M⌉ := by nlinarith [sq_nonneg ((k : ℝ) - 1), sq_nonneg (k : ℝ)]
    have h2 : (-⌈1 + M⌉ : ℝ) ≤ k := by nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg (k : ℝ)]
    exact ⟨by exact_mod_cast h2, by exact_mod_cast h1⟩
  refine (((Set.finite_Icc (-⌈1 + M⌉) ⌈1 + M⌉).prod (Set.finite_Icc (-⌈1 + M⌉) ⌈1 + M⌉)).image
    fun x : ℤ × ℤ => ((⟨x.1, x.2⟩ : GaussianInt) : ℂ)).subset ?_
  rintro w ⟨⟨z, rfl⟩, hw⟩
  rw [Complex.normSq_apply, ← GaussianInt.intCast_re, ← GaussianInt.intCast_im] at hw
  exact ⟨(z.re, z.im), ⟨key _ (by nlinarith [mul_self_nonneg (z.im : ℝ)]),
    key _ (by nlinarith [mul_self_nonneg (z.re : ℝ)])⟩, rfl⟩

/-- Only finitely many elements of the Picard group have all their entries in a disc. -/
theorem finite_picard_entries_le (M : ℝ) :
    {g : SL(2, ℂ) | g ∈ picard ∧ ∀ i j, Complex.normSq (g i j) ≤ M}.Finite := by
  have hS := Set.Finite.pi (ι := Fin 2) fun _ => Set.Finite.pi (ι := Fin 2) fun _ =>
    finite_gaussianInt_normSq_le M
  refine (hS.preimage (f := fun (g : SL(2, ℂ)) (i j : Fin 2) => g i j)
    fun g₁ _ g₂ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j =>
      congrFun (congrFun h i) j).subset ?_
  rintro g ⟨hg, hb⟩
  simp only [Set.mem_preimage, Set.mem_univ_pi]
  exact fun i j => ⟨entry_mem_of_mem_picard hg i j, hb i j⟩

/-- Only finitely many elements of the Picard group move a compact set to meet itself. -/
theorem finite_picard_smul_inter (K : Set H3) (hK : IsCompact K) :
    {g : SL(2, ℂ) | g ∈ picard ∧ ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite := by
  obtain ⟨t₀, T, R, ht₀, hbox⟩ := exists_box_of_isCompact hK
  refine (finite_picard_entries_le (entryBound t₀ T R)).subset ?_
  rintro g ⟨hg, _, ⟨p, hp, rfl⟩, hgp⟩
  exact ⟨hg, entries_bound g ht₀ (hbox p hp) (hbox _ hgp)⟩

/-- **M2.4.** Every subgroup of the Picard group acts properly discontinuously on `ℍ³`. -/
theorem properlyDiscontinuous_of_le_picard {Γ : Subgroup SL(2, ℂ)} (hΓ : Γ ≤ picard)
    (K : Set H3) (hK : IsCompact K) :
    {g : Γ | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite :=
  ((finite_picard_smul_inter K hK).preimage Subtype.val_injective.injOn).subset
    fun g hg => ⟨hΓ g.2, hg⟩

/-- In particular the Picard group itself acts properly discontinuously. -/
theorem picard_properlyDiscontinuous (K : Set H3) (hK : IsCompact K) :
    {g : picard | ((fun p : H3 => g • p) '' K ∩ K).Nonempty}.Finite :=
  properlyDiscontinuous_of_le_picard le_rfl K hK

end Picard

/-! ## Toward Milestone 2: a torsion-free subgroup of finite index

The principal congruence subgroup `Γ(2 + i)`: the matrices of `SL(2, ℤ[i])` congruent to the
identity modulo the prime `2 + i`, of norm `5`. It has finite index, being the kernel of
reduction to the finite group `SL(2, ℤ[i]/(2 + i))`, and it acts freely. At a fixed point
`q = z + t j` of `g`, the `j` and `k` parts of `q (c q + d) = a q + b` give
`a = 2 Re(c z) + conj d`, so `tr g = 2 Re(c z + d)` is real, and the heights give
`|c q + d| = 1`, so `|tr g| ≤ 2`. For `g ∈ Γ(2 + i)` the trace is a Gaussian integer congruent
to `2`, and the only one in `[-2, 2]` is `2` itself; a fixed point with trace `2` forces `c = 0`,
`a = d = 1` and `b = 0`. (So `-I`, of trace `-2`, is not in `Γ(2 + i)` either.) With M2.2–M2.4
this makes `Γ(2 + i)` a Kleinian group. -/

section Congruence

open MatrixGroups Quaternion

/-- The real algebra at a fixed point. The variables are the coordinates of `q = x + y i + t j`
and the real and imaginary parts of the entries; the hypotheses are the four components of
`q (c q + d) = a q + b` and `|c q + d|² = 1`. -/
theorem fixed_point_real (x y t a₁ a₂ b₁ b₂ c₁ c₂ d₁ d₂ : ℝ) (ht : 0 < t)
    (e₀ : x * (c₁ * x - c₂ * y + d₁) - y * (c₁ * y + c₂ * x + d₂) - t * (c₁ * t) =
      a₁ * x - a₂ * y + b₁)
    (e₁ : x * (c₁ * y + c₂ * x + d₂) + y * (c₁ * x - c₂ * y + d₁) + t * (c₂ * t) =
      a₁ * y + a₂ * x + b₂)
    (e₂ : t * (2 * (c₁ * x - c₂ * y) + d₁) = a₁ * t)
    (e₃ : -(t * d₂) = a₂ * t)
    (hN : (c₁ * x - c₂ * y + d₁) ^ 2 + (c₁ * y + c₂ * x + d₂) ^ 2 + (c₁ * t) ^ 2 +
      (c₂ * t) ^ 2 = 1) :
    a₂ + d₂ = 0 ∧ -2 ≤ a₁ + d₁ ∧ a₁ + d₁ ≤ 2 ∧
      (a₁ + d₁ = 2 →
        a₁ = 1 ∧ a₂ = 0 ∧ b₁ = 0 ∧ b₂ = 0 ∧ c₁ = 0 ∧ c₂ = 0 ∧ d₁ = 1 ∧ d₂ = 0) := by
  have ht0 : t ≠ 0 := ht.ne'
  have ha₁ : a₁ = 2 * (c₁ * x - c₂ * y) + d₁ :=
    mul_right_cancel₀ ht0 (by linear_combination (-1 : ℝ) * e₂)
  have ha₂ : a₂ = -d₂ := mul_right_cancel₀ ht0 (by linear_combination (-1 : ℝ) * e₃)
  have htr : a₁ + d₁ = 2 * (c₁ * x - c₂ * y + d₁) := by linear_combination ha₁
  have hm : (c₁ * x - c₂ * y + d₁) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
  refine ⟨by linear_combination ha₂, by nlinarith [sq_nonneg (c₁ * x - c₂ * y + d₁ + 1)],
    by nlinarith [sq_nonneg (c₁ * x - c₂ * y + d₁ - 1)], fun h2 => ?_⟩
  have hm1 : c₁ * x - c₂ * y + d₁ = 1 := by linarith
  have hS : (c₁ * y + c₂ * x + d₂) ^ 2 + (c₁ * t) ^ 2 + (c₂ * t) ^ 2 = 0 := by
    linear_combination hN - (c₁ * x - c₂ * y + d₁ + 1) * hm1
  have hc₁ : c₁ = 0 := by
    have h : (c₁ * t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)).resolve_right ht0
  have hc₂ : c₂ = 0 := by
    have h : (c₂ * t) ^ 2 = 0 := by
      nlinarith [sq_nonneg (c₁ * y + c₂ * x + d₂), sq_nonneg (c₁ * t), sq_nonneg (c₂ * t)]
    exact (mul_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h)).resolve_right ht0
  subst hc₁ hc₂
  have hd₁ : d₁ = 1 := by linear_combination hm1
  have hd₂ : d₂ = 0 := (pow_eq_zero_iff two_ne_zero).1 (by linear_combination hS)
  subst hd₁ hd₂
  have ha₁' : a₁ = 1 := by linear_combination ha₁
  have ha₂' : a₂ = 0 := by linear_combination ha₂
  subst ha₁' ha₂'
  exact ⟨rfl, rfl, by linear_combination (-1 : ℝ) * e₀, by linear_combination (-1 : ℝ) * e₁,
    rfl, rfl, rfl, rfl⟩

/-- At a fixed point of `g` the trace is real and lies in `[-2, 2]`, and it is `2` only for
`g = 1`. -/
theorem fixed_point_trace (g : SL(2, ℂ)) (p : H3) (hfix : g • p = p) :
    (g 0 0 + g 1 1).im = 0 ∧ -2 ≤ (g 0 0 + g 1 1).re ∧ (g 0 0 + g 1 1).re ≤ 2 ∧
      (g 0 0 + g 1 1 = 2 → g = 1) := by
  have hK := toQ_imK p
  have hM0 := denom_ne_zero (sl2_row_ne_zero g) hK p.2
  -- `q (c q + d) = a q + b`
  have hq : toQ p * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
      ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
    have e : mobiusQ g (toQ p) * (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) =
        ((g 0 0 : ℂ) : ℍ) * toQ p + ((g 0 1 : ℂ) : ℍ) := by
      unfold mobiusQ
      exact inv_mul_cancel_right₀ hM0 _
    rwa [← toQ_smul, hfix] at e
  -- `|c q + d|² = 1`, since the height is unchanged
  have hN : normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = 1 := by
    have hh := smul_height g p
    rw [hfix, eq_div_iff (normSq_pos hM0).ne'] at hh
    exact mul_left_cancel₀ p.2.ne' (hh.trans (mul_one _).symm)
  have e₀ := congrArg QuaternionAlgebra.re hq
  have e₁ := congrArg QuaternionAlgebra.imI hq
  have e₂ := congrArg QuaternionAlgebra.imJ hq
  have e₃ := congrArg QuaternionAlgebra.imK hq
  rw [normSq_def'] at hN
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    re_coeComplex, imI_coeComplex, imJ_coeComplex, imK_coeComplex, hK] at e₀ e₁ e₂ e₃ hN
  obtain ⟨h1, h2, h3, h4⟩ := fixed_point_real (toQ p).re (toQ p).imI (toQ p).imJ
    (g 0 0).re (g 0 0).im (g 0 1).re (g 0 1).im (g 1 0).re (g 1 0).im (g 1 1).re (g 1 1).im
    (toQ_imJ_pos p) (by linear_combination e₀) (by linear_combination e₁)
    (by linear_combination e₂) (by linear_combination e₃) (by linear_combination hN)
  refine ⟨by simpa using h1, by simpa using h2, by simpa using h3, fun htr => ?_⟩
  have htr' : (g 0 0).re + (g 1 1).re = 2 := by simpa using congrArg Complex.re htr
  obtain ⟨ha₁, ha₂, hb₁, hb₂, hc₁, hc₂, hd₁, hd₂⟩ := h4 htr'
  have e00 : g 0 0 = 1 := Complex.ext (by simpa using ha₁) (by simpa using ha₂)
  have e01 : g 0 1 = 0 := Complex.ext (by simpa using hb₁) (by simpa using hb₂)
  have e10 : g 1 0 = 0 := Complex.ext (by simpa using hc₁) (by simpa using hc₂)
  have e11 : g 1 1 = 1 := Complex.ext (by simpa using hd₁) (by simpa using hd₂)
  refine Matrix.SpecialLinearGroup.ext _ _
    (Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩)
  · simp [e00]
  · simp [e01]
  · simp [e10]
  · simp [e11]

/-- The ideal `(2 + i)` of `ℤ[i]`, of norm `5`. -/
def idealTwoI : Ideal GaussianInt := Ideal.span {⟨2, 1⟩}

/-- Every Gaussian integer is congruent modulo `2 + i` to one of `0, …, 4`, because
`i ≡ -2` and `5 = (2 + i)(2 - i)`. -/
instance : Finite (GaussianInt ⧸ idealTwoI) := by
  refine Set.finite_univ_iff.1 (((Set.finite_Icc (0 : ℤ) 4).image
    fun n : ℤ => Ideal.Quotient.mk idealTwoI (n : GaussianInt)).subset ?_)
  rintro x -
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine ⟨(z.re - 2 * z.im) % 5, ⟨by omega, by omega⟩, ?_⟩
  show Ideal.Quotient.mk idealTwoI (((z.re - 2 * z.im) % 5 : ℤ) : GaussianInt) =
    Ideal.Quotient.mk idealTwoI z
  rw [Ideal.Quotient.eq, idealTwoI, Ideal.mem_span_singleton]
  refine ⟨⟨-z.im - 2 * ((z.re - 2 * z.im) / 5), (z.re - 2 * z.im) / 5⟩, ?_⟩
  ext <;> (simp; try omega)

instance : Finite SL(2, GaussianInt ⧸ idealTwoI) :=
  Finite.of_injective (fun (g : SL(2, GaussianInt ⧸ idealTwoI)) (i j : Fin 2) => g i j)
    fun _ _ h => Matrix.SpecialLinearGroup.ext _ _ fun i j => congrFun (congrFun h i) j

/-- The principal congruence subgroup `Γ(2 + i)` of `SL(2, ℤ[i])`: the kernel of reduction
modulo `2 + i`. -/
def gammaTwoIZ : Subgroup SL(2, GaussianInt) :=
  (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealTwoI)).ker

/-- `Γ(2 + i)` as a subgroup of `SL(2, ℂ)`, inside the Picard group. -/
noncomputable def gammaTwoI : Subgroup SL(2, ℂ) :=
  gammaTwoIZ.map (Matrix.SpecialLinearGroup.map GaussianInt.toComplex)

theorem gammaTwoI_le_picard : gammaTwoI ≤ picard := by
  rintro _ ⟨h, -, rfl⟩
  exact ⟨h, rfl⟩

theorem sl2Map_injective :
    Function.Injective (Matrix.SpecialLinearGroup.map GaussianInt.toComplex :
      SL(2, GaussianInt) →* SL(2, ℂ)) := fun g₁ g₂ h =>
  Matrix.SpecialLinearGroup.ext _ _ fun i j => GaussianInt.toComplex_injective (by
    simpa using congrArg (fun g : SL(2, ℂ) => g i j) h)

/-- **M2.5, finite index.** `Γ(2 + i)` has finite index in the Picard group. -/
theorem relIndex_gammaTwoI_picard : gammaTwoI.relIndex picard ≠ 0 := by
  rw [gammaTwoI, picard, MonoidHom.range_eq_map,
    Subgroup.relIndex_map_map_of_injective _ _ sl2Map_injective, Subgroup.relIndex_top_right]
  show (Matrix.SpecialLinearGroup.map (Ideal.Quotient.mk idealTwoI)).ker.index ≠ 0
  exact Subgroup.FiniteIndex.index_ne_zero

theorem sub_one_mem_of_mem_gammaTwoIZ {h : SL(2, GaussianInt)} (hh : h ∈ gammaTwoIZ)
    (i : Fin 2) : h i i - 1 ∈ idealTwoI := by
  rw [gammaTwoIZ, MonoidHom.mem_ker] at hh
  have e := congrArg (fun g : SL(2, GaussianInt ⧸ idealTwoI) => g i i) hh
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at e
  rw [← map_one (Ideal.Quotient.mk idealTwoI), Ideal.Quotient.eq] at e
  exact e

theorem trace_sub_two_mem {h : SL(2, GaussianInt)} (hh : h ∈ gammaTwoIZ) :
    h 0 0 + h 1 1 - 2 ∈ idealTwoI := by
  have := add_mem (sub_one_mem_of_mem_gammaTwoIZ hh 0) (sub_one_mem_of_mem_gammaTwoIZ hh 1)
  convert this using 1
  ring

/-- The only Gaussian integer in `[-2, 2]` congruent to `2` modulo `2 + i` is `2`: the
difference is `-5 w₂` for the imaginary part `w₂` of the quotient, and lies in `[-4, 0]`. -/
theorem eq_two_of_sub_two_mem {τ : GaussianInt} (hmem : τ - 2 ∈ idealTwoI) (him : τ.im = 0)
    (hlo : -2 ≤ τ.re) (hhi : τ.re ≤ 2) : τ = 2 := by
  rw [idealTwoI, Ideal.mem_span_singleton] at hmem
  obtain ⟨w, hw⟩ := hmem
  have hre := congrArg Zsqrtd.re hw
  have hi := congrArg Zsqrtd.im hw
  simp at hre hi
  ext <;> simp <;> omega

/-- **M2.5, freeness.** No element of `Γ(2 + i)` other than the identity fixes a point. -/
theorem gammaTwoI_free {g : SL(2, ℂ)} (hg : g ∈ gammaTwoI) (hne : g ≠ 1) (p : H3) :
    g • p ≠ p := by
  intro hfix
  obtain ⟨him, hlo, hhi, hone⟩ := fixed_point_trace g p hfix
  refine hne (hone ?_)
  obtain ⟨h, hh, rfl⟩ := hg
  have htr : (Matrix.SpecialLinearGroup.map GaussianInt.toComplex h) 0 0 +
      (Matrix.SpecialLinearGroup.map GaussianInt.toComplex h) 1 1 =
      ((h 0 0 + h 1 1 : GaussianInt) : ℂ) := by simp
  rw [htr] at him hlo hhi ⊢
  rw [← GaussianInt.intCast_im] at him
  rw [← GaussianInt.intCast_re] at hlo hhi
  rw [eq_two_of_sub_two_mem (trace_sub_two_mem hh) (by exact_mod_cast him)
    (by exact_mod_cast hlo) (by exact_mod_cast hhi)]
  exact map_ofNat GaussianInt.toComplex 2

/-- `Γ(2 + i)` is a Kleinian group: isometries (M2.2) preserving the volume (M2.3), acting
freely (M2.5) and properly discontinuously (M2.4). -/
theorem isKleinian_gammaTwoI : IsKleinian gammaTwoI where
  isometry g p q := hdist_smul (g : SL(2, ℂ)) p q
  measure_preserving g := measurePreserving_smul (g : SL(2, ℂ))
  free g hg p := gammaTwoI_free g.2 (fun h => hg (Subtype.ext h)) p
  properly_discontinuous := properlyDiscontinuous_of_le_picard gammaTwoI_le_picard

end Congruence

/-! ## Toward Milestone 2: a fundamental domain of finite positive volume

No explicit fundamental domain is needed. A free, properly discontinuous action by
homeomorphisms of a second countable space has a measurable fundamental domain: cover the space
by countably many open sets `U n` that no nontrivial element maps into themselves, and keep a
point of `U n` when its orbit misses every earlier `U m`. Its volume is at most that of any set
meeting every orbit. For `Γ(2 + i)` such a set is a finite union of translates of the reduction
box `|x|, |y| ≤ ½`, `|q| ≥ 1` of the Picard group — finite because `Γ(2 + i)` has finite index —
and the box has finite volume, since it sits above height `½`. Positivity is `hvol ≠ 0`. -/

section FundamentalDomainExistence

open Filter Topology Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

/-- For a free, properly discontinuous action by homeomorphisms, every point has a neighbourhood
that no element other than the identity maps into itself. -/
theorem exists_nhds_smul_notMem [TopologicalSpace X] [T2Space X]
    [WeaklyLocallyCompactSpace X]
    (hcont : ∀ g : G, Continuous fun x : X => g • x)
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x)
    (hpd : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite) (x : X) :
    ∃ N ∈ 𝓝 x, ∀ g : G, g ≠ 1 → ∀ y ∈ N, g • y ∉ N := by
  obtain ⟨K, hK, hKx⟩ := WeaklyLocallyCompactSpace.exists_compact_mem_nhds x
  -- each `g ≠ 1` moves `x`, so it moves a whole neighbourhood of `x` off itself
  have hloc : ∀ g : G, ∃ N ∈ 𝓝 x, g ≠ 1 → ∀ y ∈ N, g • y ∉ N := by
    intro g
    by_cases hg : g = 1
    · exact ⟨Set.univ, univ_mem, fun h => absurd hg h⟩
    obtain ⟨V, W, hV, hW, hxV, hgxW, hVW⟩ := t2_separation (hfree g hg x).symm
    refine ⟨V ∩ (fun y => g • y) ⁻¹' W, inter_mem (hV.mem_nhds hxV)
      ((hcont g).continuousAt.preimage_mem_nhds (hW.mem_nhds hgxW)), fun _ y hy hgy => ?_⟩
    exact Set.disjoint_left.1 hVW hgy.1 hy.2
  choose N hN hNsep using hloc
  -- only the finitely many `g` that move `K` to meet itself need to be handled
  refine ⟨K ∩ ⋂ g ∈ {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}, N g,
    inter_mem hKx ((biInter_mem (hpd K hK)).2 fun g _ => hN g), ?_⟩
  rintro g hg y ⟨hyK, hyN⟩ ⟨hgyK, hgyN⟩
  have hgS : g ∈ {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty} :=
    ⟨g • y, ⟨y, hyK, rfl⟩, hgyK⟩
  exact hNsep g hg y (Set.mem_iInter₂.1 hyN g hgS) (Set.mem_iInter₂.1 hgyN g hgS)

/-- **A fundamental domain for a free, properly discontinuous action.** Cover the space by
countably many open sets `U n` that no nontrivial element maps into themselves, and let `F`
consist of the points of `U n` whose orbit misses `U m` for every `m < n`. Every orbit meets `F`,
at the first `n` whose `U n` it meets, and meets it only once. -/
theorem exists_isFundamentalDomain [TopologicalSpace X] [T2Space X]
    [WeaklyLocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [Countable G]
    (hcont : ∀ g : G, Continuous fun x : X => g • x)
    (hfree : ∀ g : G, g ≠ 1 → ∀ x : X, g • x ≠ x)
    (hpd : ∀ K : Set X, IsCompact K →
      {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite) (μ : Measure X) :
    ∃ F : Set X, IsFundamentalDomain G F μ := by
  rcases isEmpty_or_nonempty X with hX | hX
  · exact ⟨∅, IsFundamentalDomain.mk' MeasurableSet.empty.nullMeasurableSet
      fun x => (hX.false x).elim⟩
  choose N hN hsep using exists_nhds_smul_notMem hcont hfree hpd
  obtain ⟨s, hsc, hsU⟩ :=
    TopologicalSpace.countable_cover_nhds fun x => interior_mem_nhds.2 (hN x)
  have hs : s.Nonempty := by
    obtain ⟨x⟩ := hX
    have hx : x ∈ ⋃ y ∈ s, interior (N y) := by rw [hsU]; trivial
    obtain ⟨y, hy, -⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨y, hy⟩
  obtain ⟨c, rfl⟩ := hsc.exists_eq_range hs
  -- the open sets `U n`, and their saturations `O n`
  obtain ⟨U, hU⟩ : ∃ U : ℕ → Set X, U = fun n => interior (N (c n)) := ⟨_, rfl⟩
  obtain ⟨O, hO⟩ : ∃ O : ℕ → Set X, O = fun n => ⋃ g : G, (fun x => g • x) ⁻¹' U n :=
    ⟨_, rfl⟩
  have hUo : ∀ n, IsOpen (U n) := fun n => by rw [hU]; exact isOpen_interior
  have hOo : ∀ n, IsOpen (O n) := fun n => by
    rw [hO]; exact isOpen_iUnion fun g => (hUo n).preimage (hcont g)
  have hUsep : ∀ n (g : G), g ≠ 1 → ∀ y ∈ U n, g • y ∉ U n := by
    intro n g hg y hy hgy
    simp only [hU] at hy hgy
    exact hsep (c n) g hg y (interior_subset hy) (interior_subset hgy)
  have hcovU : ∀ x, ∃ n, x ∈ U n := by
    intro x
    have hx : x ∈ ⋃ y ∈ Set.range c, interior (N y) := by rw [hsU]; trivial
    obtain ⟨_, ⟨n, rfl⟩, hxn⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨n, by simpa only [hU] using hxn⟩
  have hmemO : ∀ n x, x ∈ O n ↔ ∃ g : G, g • x ∈ U n := by
    intro n x
    simp only [hO, Set.mem_iUnion, Set.mem_preimage]
  have hOinv : ∀ n (h : G) x, h • x ∈ O n ↔ x ∈ O n := by
    intro n h x
    rw [hmemO, hmemO]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨g * h, by rwa [mul_smul]⟩
    · rintro ⟨g, hg⟩
      exact ⟨g * h⁻¹, by rwa [mul_smul, inv_smul_smul]⟩
  -- the domain
  obtain ⟨F, hF⟩ : ∃ F : Set X, F = ⋃ n, U n \ ⋃ m, ⋃ (_ : m < n), O m := ⟨_, rfl⟩
  have hmemF : ∀ x, x ∈ F ↔ ∃ n, x ∈ U n ∧ ∀ m < n, x ∉ O m := by
    intro x
    simp only [hF, Set.mem_iUnion, Set.mem_diff, not_exists]
  -- no nontrivial element maps a point of `F` into `F`
  have huniq : ∀ y (h : G), y ∈ F → h • y ∈ F → h = 1 := by
    intro y h hy hhy
    obtain ⟨n, hn, hnm⟩ := (hmemF y).1 hy
    obtain ⟨n', hn', hnm'⟩ := (hmemF _).1 hhy
    by_contra h1
    rcases lt_trichotomy n n' with hlt | rfl | hlt
    · exact hnm' n hlt ((hmemO n _).2 ⟨h⁻¹, by rwa [inv_smul_smul]⟩)
    · exact hUsep n h h1 y hn hn'
    · exact hnm n' hlt ((hmemO n' y).2 ⟨h, hn'⟩)
  refine ⟨F, IsFundamentalDomain.mk' ?_ fun x => ?_⟩
  · rw [hF]
    exact (MeasurableSet.iUnion fun n => (hUo n).measurableSet.diff
      (MeasurableSet.iUnion fun m => MeasurableSet.iUnion fun _ =>
        (hOo m).measurableSet)).nullMeasurableSet
  · classical
    have hex : ∃ n, x ∈ O n := by
      obtain ⟨n, hn⟩ := hcovU x
      exact ⟨n, (hmemO n x).2 ⟨1, by rwa [one_smul]⟩⟩
    obtain ⟨g, hg⟩ := (hmemO _ x).1 (Nat.find_spec hex)
    have hgF : g • x ∈ F := (hmemF _).2 ⟨Nat.find hex, hg, fun m hm hgm =>
      Nat.find_min hex hm ((hOinv m g x).1 hgm)⟩
    refine ⟨g, hgF, fun g' hg' => ?_⟩
    have h1 := huniq (g • x) (g' * g⁻¹) hgF (by rwa [mul_smul, inv_smul_smul])
    exact mul_inv_eq_one.1 h1

/-- A fundamental domain has at most the measure of any set meeting every orbit. -/
theorem measure_le_of_forall_exists_smul_mem [MeasurableSpace X] {μ : Measure X} [Countable G]
    [SMulInvariantMeasure G X μ] [MeasurableConstSMul G X] {F E : Set X}
    (hF : IsFundamentalDomain G F μ) (hE : ∀ x : X, ∃ g : G, g • x ∈ E) : μ F ≤ μ E := by
  calc μ F ≤ μ (⋃ g : G, g • E ∩ F) := measure_mono fun x hx => by
        obtain ⟨g, hg⟩ := hE x
        exact Set.mem_iUnion.2
          ⟨g⁻¹, Set.mem_smul_set_iff_inv_smul_mem.2 (by rwa [inv_inv]), hx⟩
    _ ≤ ∑' g : G, μ (g • E ∩ F) := measure_iUnion_le _
    _ = μ E := (hF.measure_eq_tsum E).symm

end FundamentalDomainExistence

section Covolume

open MatrixGroups Quaternion Pointwise

instance : SMulInvariantMeasure SL(2, ℂ) H3 hvol :=
  ⟨fun g _ hs => (measurePreserving_smul g).measure_preimage hs.nullMeasurableSet⟩

instance : MeasurableConstSMul SL(2, ℂ) H3 := ⟨fun g => (continuous_smul g).measurable⟩

theorem normSq_toQ (p : H3) : normSq (toQ p) = N p.1 := by
  rw [normSq_def']; simp [toQ, N]; ring

theorem T_mem_picard (z : GaussianInt) : T (z : ℂ) ∈ picard :=
  mem_picard_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨1, by simp [T]⟩, ⟨z, by simp [T]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨0, by simp [T]⟩, ⟨1, by simp [T]⟩⟩⟩)

theorem S_mem_picard : S ∈ picard :=
  mem_picard_iff.2 (Fin.forall_fin_two.2
    ⟨Fin.forall_fin_two.2 ⟨⟨0, by simp [S]⟩, ⟨-1, by simp [S]⟩⟩,
      Fin.forall_fin_two.2 ⟨⟨1, by simp [S]⟩, ⟨0, by simp [S]⟩⟩⟩)

/-- Along an orbit of the Picard group only finitely many heights are at least the starting
one: they are `t / |c q + d|²` with `|c q + d|² ≤ 1`, which bounds the Gaussian integers `c`
and `d`. -/
theorem finite_heights (p : H3) :
    ((fun g : SL(2, ℂ) => (g • p).1 2) '' {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}).Finite := by
  have ht0 : 0 < p.1 2 := p.2
  refine (((finite_gaussianInt_normSq_le (1 / p.1 2 ^ 2)).prod
    (finite_gaussianInt_normSq_le (2 * (1 + 1 / p.1 2 ^ 2 * normSq (toQ p))))).image
      fun cd : ℂ × ℂ => p.1 2 / normSq ((cd.1 : ℍ) * toQ p + (cd.2 : ℍ))).subset ?_
  rintro _ ⟨g, ⟨hg, hle⟩, rfl⟩
  have hh := smul_height g p
  have hMpos := normSq_pos (denom_ne_zero (sl2_row_ne_zero g) (toQ_imK p) p.2)
  have hc := normSq_mul_imJ_le (g 1 0) (g 1 1) (toQ_imK p)
  rw [show (toQ p).imJ = p.1 2 from rfl] at hc
  generalize hM : ((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ) = M at hh hMpos hc
  -- `|c q + d|² ≤ 1`, since the height did not drop
  have hM1 : normSq M ≤ 1 := by
    rw [hh, le_div_iff₀ hMpos] at hle
    nlinarith
  have hcb : Complex.normSq (g 1 0) ≤ 1 / p.1 2 ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hd : ((g 1 1 : ℂ) : ℍ) = M + -(((g 1 0 : ℂ) : ℍ) * toQ p) := by rw [← hM]; abel
  have hdb := normSq_add_le M (-(((g 1 0 : ℂ) : ℍ) * toQ p))
  rw [← hd, normSq_neg, map_mul, normSq_coeComplex, normSq_coeComplex] at hdb
  have hcq : Complex.normSq (g 1 0) * normSq (toQ p) ≤ 1 / p.1 2 ^ 2 * normSq (toQ p) :=
    mul_le_mul_of_nonneg_right hcb normSq_nonneg
  refine ⟨(g 1 0, g 1 1), ⟨⟨entry_mem_of_mem_picard hg 1 0, hcb⟩,
    ⟨entry_mem_of_mem_picard hg 1 1, by linarith⟩⟩, ?_⟩
  show p.1 2 / normSq (((g 1 0 : ℂ) : ℍ) * toQ p + ((g 1 1 : ℂ) : ℍ)) = (g • p).1 2
  rw [hM, hh]

/-- Every orbit of the Picard group has a point of maximal height. -/
theorem exists_max_height (p : H3) :
    ∃ g₀ ∈ picard, ∀ g ∈ picard, (g • p).1 2 ≤ (g₀ • p).1 2 := by
  have h1 : (1 : SL(2, ℂ)) ∈ {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2} :=
    ⟨picard.one_mem, by simp only [one_smul, le_refl]⟩
  have hne : ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}).Nonempty := ⟨_, 1, h1, rfl⟩
  have hbdd := (finite_heights p).bddAbove
  obtain ⟨g₀, ⟨hg₀, -⟩, hmax⟩ := hne.csSup_mem (finite_heights p)
  have hmax' : (g₀ • p).1 2 = sSup ((fun g : SL(2, ℂ) => (g • p).1 2) ''
      {g | g ∈ picard ∧ p.1 2 ≤ (g • p).1 2}) := hmax
  refine ⟨g₀, hg₀, fun g hg => ?_⟩
  rw [hmax']
  by_cases hle : p.1 2 ≤ (g • p).1 2
  · exact le_csSup hbdd ⟨g, ⟨hg, hle⟩, rfl⟩
  · exact (not_le.1 hle).le.trans (le_csSup hbdd ⟨1, h1, by simp only [one_smul]⟩)

/-- The reduction box of the Picard group: `|x|, |y| ≤ ½` and `|q| ≥ 1`. -/
def picardBox : Set H3 := {p | |p.1 0| ≤ 1 / 2 ∧ |p.1 1| ≤ 1 / 2 ∧ 1 ≤ N p.1}

/-- **Reduction.** The Picard group carries every point into the box: take a point of maximal
height on the orbit and translate it into the strip `|x|, |y| ≤ ½`; then `|q| ≥ 1`, since
otherwise `S`, which divides the height by `|q|²`, would raise it further. -/
theorem exists_smul_mem_picardBox (p : H3) : ∃ g ∈ picard, g • p ∈ picardBox := by
  obtain ⟨g₀, hg₀, hmax⟩ := exists_max_height p
  have hg₁ : T ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ) * g₀ ∈
      picard := picard.mul_mem (T_mem_picard _) hg₀
  set g₁ := T ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ) * g₀
    with hg₁def
  have hval : (g₁ • p).1 = (g₀ • p).1 +
      ![((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ).re,
        ((⟨-round ((g₀ • p).1 0), -round ((g₀ • p).1 1)⟩ : GaussianInt) : ℂ).im, 0] := by
    rw [hg₁def, mul_smul, T_smul_val]
  have h0 : |(g₁ • p).1 0| ≤ 1 / 2 := by
    rw [hval]
    simpa [GaussianInt.re_toComplex, sub_eq_add_neg] using abs_sub_round ((g₀ • p).1 0)
  have h1 : |(g₁ • p).1 1| ≤ 1 / 2 := by
    rw [hval]
    simpa [GaussianInt.im_toComplex, sub_eq_add_neg] using abs_sub_round ((g₀ • p).1 1)
  have h2 : (g₁ • p).1 2 = (g₀ • p).1 2 := by rw [hval]; simp
  refine ⟨g₁, hg₁, h0, h1, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hS10 : S 1 0 = 1 := by simp [S]
  have hS11 : S 1 1 = 0 := by simp [S]
  have hht : ((S * g₁) • p).1 2 = (g₁ • p).1 2 / N (g₁ • p).1 := by
    rw [mul_smul, smul_height S (g₁ • p), hS10, hS11, coeComplex_one, coeComplex_zero, one_mul,
      add_zero, normSq_toQ]
  have hNpos : 0 < N (g₁ • p).1 := N_pos (g₁ • p).2
  have hle := hmax _ (picard.mul_mem S_mem_picard hg₁)
  rw [hht, h2, div_le_iff₀ hNpos] at hle
  nlinarith [mul_lt_mul_of_pos_left hlt (g₀ • p).2]

/-- The box `[-½, ½]² × [½, ∞)` in `ℝ³`. -/
def tallBox : Set (Fin 3 → ℝ) :=
  Set.pi Set.univ ![Set.Icc (-(1 / 2)) (1 / 2), Set.Icc (-(1 / 2)) (1 / 2), Set.Ici (1 / 2)]

/-- The reduction box lies above height `½`: `t² ≥ 1 − x² − y² ≥ ½`. -/
theorem picardBox_subset : picardBox ⊆ Subtype.val ⁻¹' tallBox := by
  rintro p ⟨h0, h1, hN⟩
  have hx := abs_le.1 h0
  have hy := abs_le.1 h1
  have hx2 : p.1 0 * p.1 0 ≤ 1 / 4 := by nlinarith
  have hy2 : p.1 1 * p.1 1 ≤ 1 / 4 := by nlinarith
  have ht : 1 / 2 ≤ p.1 2 := by
    unfold N at hN
    nlinarith [p.2]
  refine Set.mem_univ_pi.2 fun i => ?_
  fin_cases i
  · exact ⟨hx.1, hx.2⟩
  · exact ⟨hy.1, hy.2⟩
  · exact ht

set_option maxHeartbeats 400000 in
/-- The box `[-½, ½]² × [½, ∞)` has finite hyperbolic volume, `∫_{½}^∞ t⁻³ dt` being finite. -/
theorem hvol_tallBox_lt_top : hvol (Subtype.val ⁻¹' tallBox) < ⊤ := by
  set S : Fin 3 → Set ℝ :=
    ![Set.Icc (-(1 / 2)) (1 / 2), Set.Icc (-(1 / 2)) (1 / 2), Set.Ici (1 / 2)] with hS
  set h : Fin 3 → ℝ → ℝ := ![fun _ => 1, fun _ => 1, fun t => (t ^ 3)⁻¹] with hh
  set f : Fin 3 → ℝ → ℝ := fun i => (S i).indicator (h i) with hf
  have hSm : ∀ i, MeasurableSet (S i) := by
    intro i; fin_cases i
    · exact measurableSet_Icc
    · exact measurableSet_Icc
    · exact measurableSet_Ici
  have hBm : MeasurableSet tallBox := MeasurableSet.univ_pi hSm
  have hBsub : tallBox ⊆ Set.range (Subtype.val : H3 → Fin 3 → ℝ) := by
    intro x hx
    have h2 : x 2 ∈ Set.Ici (1 / 2 : ℝ) := Set.mem_univ_pi.1 hx 2
    exact ⟨⟨x, lt_of_lt_of_le (by norm_num) h2⟩, rfl⟩
  rw [hvol_apply (measurableEmbedding_val.measurable hBm), Set.image_preimage_eq_of_subset hBsub,
    ← lintegral_indicator hBm]
  -- the integrand is a product of one-variable functions
  have hpt : ∀ x, tallBox.indicator ρ x = ENNReal.ofReal (∏ i, f i (x i)) := by
    intro x
    by_cases hx : x ∈ tallBox
    · have hxi : ∀ i, x i ∈ S i := Set.mem_univ_pi.1 hx
      rw [Set.indicator_of_mem hx, Fin.prod_univ_three]
      simp only [hf, Set.indicator_of_mem (hxi 0), Set.indicator_of_mem (hxi 1),
        Set.indicator_of_mem (hxi 2), hh]
      simp [ρ]
    · rw [Set.indicator_of_notMem hx]
      obtain ⟨i, hi⟩ : ∃ i, x i ∉ S i := by
        by_contra hcon
        push_neg at hcon
        exact hx (Set.mem_univ_pi.2 hcon)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hf, Set.indicator_of_notMem hi])]
      simp
  have hfi : ∀ i, Integrable (f i) := by
    intro i; fin_cases i
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · exact (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc
    · show Integrable ((Set.Ici (1 / 2 : ℝ)).indicator fun t => (t ^ 3)⁻¹)
      refine (integrable_indicator_iff measurableSet_Ici).2 ?_
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      refine (integrableOn_Ioi_rpow_of_lt (a := -3) (by norm_num)
        (by norm_num : (0 : ℝ) < 1 / 2)).congr_fun (fun t ht => ?_) measurableSet_Ioi
      have ht0 : (0 : ℝ) ≤ t := (lt_trans (by norm_num) ht).le
      simp [Real.rpow_neg ht0]
  simp_rw [hpt]
  exact (Integrable.fintype_prod hfi).lintegral_lt_top

instance : Countable gammaTwoI :=
  countable_of_properlyDiscontinuous basepoint
    (properlyDiscontinuous_of_le_picard gammaTwoI_le_picard)

/-- **M2.6.** `Γ(2 + i)` has a fundamental domain of finite, positive hyperbolic volume. -/
theorem exists_fundamentalDomain_gammaTwoI :
    ∃ F : Set H3, IsFundamentalDomain gammaTwoI F hvol ∧ 0 < hvol F ∧ hvol F < ⊤ := by
  obtain ⟨F, hF⟩ := exists_isFundamentalDomain (G := ↥gammaTwoI) (X := H3)
    (fun g => continuous_smul (g : SL(2, ℂ)))
    (fun g hg p => gammaTwoI_free g.2 (fun h => hg (Subtype.ext h)) p)
    (properlyDiscontinuous_of_le_picard gammaTwoI_le_picard) hvol
  refine ⟨F, hF, pos_iff_ne_zero.2 (hF.measure_ne_zero hvol_ne_zero), ?_⟩
  -- finitely many translates of the box meet every orbit of `Γ(2 + i)`
  haveI : (gammaTwoI.subgroupOf picard).FiniteIndex := ⟨relIndex_gammaTwoI_picard⟩
  haveI : Fintype (picard ⧸ gammaTwoI.subgroupOf picard) := Fintype.ofFinite _
  have hcov : ∀ p : H3, ∃ γ : gammaTwoI, γ • p ∈
      ⋃ q : picard ⧸ gammaTwoI.subgroupOf picard,
        ((Quotient.out q : picard) : SL(2, ℂ))⁻¹ • picardBox := by
    intro p
    obtain ⟨g, hg, hgp⟩ := exists_smul_mem_picardBox p
    have hmem : (Quotient.out ((⟨g, hg⟩ : picard) : picard ⧸ gammaTwoI.subgroupOf picard))⁻¹ *
        ⟨g, hg⟩ ∈ gammaTwoI.subgroupOf picard := by
      have := QuotientGroup.eq.mp
        (QuotientGroup.out_eq' ((⟨g, hg⟩ : picard) : picard ⧸ gammaTwoI.subgroupOf picard))
      simpa using this
    refine ⟨⟨_, Subgroup.mem_subgroupOf.1 hmem⟩, Set.mem_iUnion.2
      ⟨((⟨g, hg⟩ : picard) : picard ⧸ gammaTwoI.subgroupOf picard), ?_⟩⟩
    show (((Quotient.out ((⟨g, hg⟩ : picard) : picard ⧸ gammaTwoI.subgroupOf picard))⁻¹ *
      ⟨g, hg⟩ : picard) : SL(2, ℂ)) • p ∈ _
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_smul]
    exact Set.smul_mem_smul_set hgp
  have hEfin : hvol (⋃ q : picard ⧸ gammaTwoI.subgroupOf picard,
      ((Quotient.out q : picard) : SL(2, ℂ))⁻¹ • picardBox) < ⊤ := by
    refine (measure_iUnion_le _).trans_lt ?_
    rw [tsum_fintype]
    simp only [measure_smul]
    rw [Finset.sum_const, nsmul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _)
      ((measure_mono picardBox_subset).trans_lt hvol_tallBox_lt_top)
  exact (measure_le_of_forall_exists_smul_mem hF hcov).trans_lt hEfin

end Covolume

end Thurston23

open MeasureTheory Thurston23 in
theorem solution : Thurston23.hyperbolicVolumes.Nonempty := by
  obtain ⟨F, hF, hpos, hfin⟩ := exists_fundamentalDomain_gammaTwoI
  exact ⟨(hvol F).toReal, ↥gammaTwoI, inferInstance, inferInstance, isKleinian_gammaTwoI, F, hF,
    (ENNReal.ofReal_toReal hfin.ne).symm, ENNReal.toReal_pos hpos.ne' hfin.ne⟩
