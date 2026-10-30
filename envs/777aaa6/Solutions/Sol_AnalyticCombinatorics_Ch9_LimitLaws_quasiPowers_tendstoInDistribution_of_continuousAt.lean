-- Prove2me | solution 1 for AnalyticCombinatorics.Ch9.LimitLaws.quasiPowers_tendstoInDistribution_of_continuousAt
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-26T10:33:57.919897+00:00
-- url     : https://prove2.me/submissions/c8305b8e-0491-4eb1-b802-f96a69451878

import Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_QuasiPowers
import Mathlib
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.Order.Filter.ENNReal
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Filter BoundedContinuousFunction Real RCLike MeasureTheory ENNReal
open scoped Topology RealInnerProductSpace ENNReal NNReal

namespace AnalyticCombinatorics.Compatibility

section ENNRealLimsup
variable {α : Type*} {f : Filter α}

lemma ofReal_limsup_toReal [f.NeBot] {u : α → ℝ≥0∞} {C : ℝ≥0} (hf : ∀ᶠ a in f, u a ≤ C) :
    ENNReal.ofReal (limsup (fun a ↦ (u a).toReal) f) = limsup u f := by
  have h₁ : IsCoboundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) :=
    IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ by positivity
  have h₂ : IsBoundedUnder (· ≤ ·) f (fun a ↦ (u a).toReal) := by
    refine isBoundedUnder_of_eventually_le (a := C) ?_
    filter_upwards [hf] with a ha
    exact ENNReal.toReal_le_coe_of_le_coe ha
  refine (ENNReal.ofReal_limsup h₁ h₂).trans (limsup_congr ?_)
  filter_upwards [hf] with x hx
  exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp : C ≠ ∞) hx)

end ENNRealLimsup

section Tightness
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] {𝕜 : Type*} [RCLike 𝕜]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [MeasurableSpace E] [BorelSpace E]
  {μ : ℕ → Measure E} [∀ i, IsFiniteMeasure (μ i)]
variable (𝕜)

lemma isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one
    (h : ∀ y, ‖y‖ = 1 →
      Tendsto (fun r : ℝ ↦ limsup (fun n ↦ (μ n).real {x | r < ‖⟪y, x⟫_𝕜‖}) atTop) atTop (𝓝 0))
    (C : ℝ≥0) (hμ : ∀ᶠ n in atTop, μ n .univ ≤ C) :
    IsTightMeasureSet (Set.range μ) := by
  refine isTightMeasureSet_range_of_tendsto_limsup_inner_of_norm_eq_one 𝕜 fun z hz ↦ ?_
  have h_ofReal (r : ℝ) : limsup (fun n ↦ μ n {x | r < ‖⟪z, x⟫_𝕜‖}) atTop
      = ENNReal.ofReal (limsup (fun n ↦ (μ n).real {x | r < ‖⟪z, x⟫_𝕜‖}) atTop) := by
    simp_rw [measureReal_def]
    rw [ofReal_limsup_toReal (C := C)]
    filter_upwards [hμ] with n hμn using (measure_mono (Set.subset_univ _)).trans hμn
  simpa only [h_ofReal, ← ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal (h z hz)

end Tightness

section Levy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If the characteristic functions of a sequence of measures `μ : ℕ → Measure E` converge pointwise
to a function which is continuous at 0, then `{μ n | n}` is tight. -/
lemma isTightMeasureSet_of_tendsto_charFun {μ : ℕ → Measure E} [∀ i, IsProbabilityMeasure (μ i)]
    {f : E → ℂ} (hf : ContinuousAt f 0)
    (h : ∀ t, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (Set.range μ) := by
  -- it suffices to show that a limsup tends to 0
  refine isTightMeasureSet_range_of_tendsto_limsup_measureReal_inner_of_norm_eq_one ℝ
    (fun z hz ↦ ?_) 1 (.of_forall fun _ ↦ by simp)
  -- first, prove an auxiliary inequality that will be used to bound the limsup
  have h_le_4 n r (hr : 0 < r) :
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ ≤ 4 := by
    have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
    calc 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - charFun (μ n) (t • z)‖ := by
      grw [neg_mul, intervalIntegral.norm_integral_le_integral_norm hr']
    _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, 2 := by
      gcongr
      rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
      refine integral_mono_of_nonneg ?_ (by fun_prop) ?_
      · exact ae_of_all _ fun _ ↦ by positivity
      · exact ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
    _ ≤ 4 := by
      simp only [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
      field_simp
      norm_num
  have h_le n r (hr : 0 < r) : (μ n).real {x | r < |⟪z, x⟫|} ≤
      2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖ :=
    measureReal_abs_inner_gt_le_integral_charFun hr
  -- We introduce an upper bound for the limsup.
  -- This is where we use that `charFun (μ n)` converges to `f`.
  have h_limsup_le r (hr : 0 < r) :
      limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
        ≤ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
    calc limsup (fun n ↦ (μ n).real {x | r < |⟪z, x⟫|}) atTop
    _ ≤ limsup (fun n ↦ 2⁻¹ * r
        * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - charFun (μ n) (t • z)‖) atTop := by
      refine limsup_le_limsup (.of_forall fun n ↦ h_le n r hr) ?_ ?_
      · exact IsCoboundedUnder.of_frequently_ge <| .of_forall fun _ ↦ ENNReal.toReal_nonneg
      · refine ⟨4, ?_⟩
        simp only [eventually_map, eventually_atTop, ge_iff_le]
        exact ⟨0, fun n _ ↦ h_le_4 n r hr⟩
    _ = 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖ := by
      refine ((Tendsto.norm ?_).const_mul _).limsup_eq
      simp only [neg_mul]
      have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
      simp_rw [intervalIntegral.integral_of_le hr']
      refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2) ?_ (by fun_prop) ?_ ?_
      · exact fun _ ↦ Measurable.aestronglyMeasurable <| by fun_prop
      · exact fun _ ↦ ae_of_all _ fun _ ↦ norm_one_sub_charFun_le_two
      · exact ae_of_all _ fun _ ↦ tendsto_const_nhds.sub (h _)
  -- It suffices to show that the upper bound tends to 0.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (h := fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) ?_ ?_ ?_
  rotate_left
  · filter_upwards [eventually_gt_atTop 0] with r hr
    refine le_limsup_of_le ?_ fun u hu ↦ ?_
    · refine ⟨4, ?_⟩
      simp only [eventually_map, eventually_atTop, ge_iff_le]
      exact ⟨0, fun n _ ↦ (h_le n r hr).trans (h_le_4 n r hr)⟩
    · exact ENNReal.toReal_nonneg.trans hu.exists.choose_spec
  · filter_upwards [eventually_gt_atTop 0] with r hr using h_limsup_le r hr
  -- We now show that the upper bound tends to 0.
  -- This will follow from the fact that `f` is continuous at `0`.
  -- `⊢ Tendsto (fun r ↦ 2⁻¹ * r * ‖∫ t in -2 * r⁻¹..2 * r⁻¹, 1 - f (t • z)‖) atTop (𝓝 0)`
  have hf_tendsto := hf.tendsto
  rw [Metric.tendsto_nhds_nhds] at hf_tendsto
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hf0 : f 0 = 1 := by symm; simpa using h 0
  simp only [gt_iff_lt, dist_eq_norm_sub', zero_sub, norm_neg, hf0] at hf_tendsto
  simp only [ge_iff_le, neg_mul, dist_zero_right, norm_mul, norm_inv,
    Real.norm_ofNat, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  obtain ⟨δ, hδ, hδ_lt⟩ : ∃ δ, 0 < δ ∧ ∀ ⦃x : E⦄, ‖x‖ < δ → ‖1 - f x‖ < ε / 4 :=
    hf_tendsto (ε / 4) (by positivity)
  refine ⟨4 * δ⁻¹, fun r hrδ ↦ ?_⟩
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrδ
  have hr' : -(2 * r⁻¹) ≤ 2 * r⁻¹ := by rw [neg_le_self_iff]; positivity
  have h_le_Ioc x (hx : x ∈ Set.Ioc (-(2 * r⁻¹)) (2 * r⁻¹)) : ‖1 - f (x • z)‖ ≤ ε / 4 := by
    refine (hδ_lt ?_).le
    simp only [norm_smul, Real.norm_eq_abs, mul_one, hz]
    calc |x|
    _ ≤ 2 * r⁻¹ := by grind
    _ < δ := by
      rw [← lt_div_iff₀' (by positivity), inv_lt_comm₀ hr (by positivity)]
      refine lt_of_lt_of_le ?_ hrδ
      field_simp
      norm_num
  rw [abs_of_nonneg hr.le]
  calc 2⁻¹ * r * ‖∫ t in -(2 * r⁻¹)..2 * r⁻¹, 1 - f (t • z)‖
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ‖1 - f (t • z)‖ := by
    grw [intervalIntegral.norm_integral_le_integral_norm hr']
  _ ≤ 2⁻¹ * r * ∫ t in -(2 * r⁻¹)..2 * r⁻¹, ε / 4 := by
    gcongr
    rw [intervalIntegral.integral_of_le hr', intervalIntegral.integral_of_le hr']
    have hf_meas : Measurable f := by
      refine measurable_of_tendsto_metrizable (f := fun n t ↦ charFun (μ n) t) (by fun_prop) ?_
      rwa [tendsto_pi_nhds]
    refine integral_mono_ae ?_ (by fun_prop) ?_
    · refine Integrable.mono' (integrable_const (ε / 4)) ?_ ?_
      · exact Measurable.aestronglyMeasurable <| by fun_prop
      · simpa using ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
    · exact ae_restrict_of_forall_mem measurableSet_Ioc h_le_Ioc
  _ = ε / 2 := by simp; field
  _ < ε := by simp [hε]

/-- Let `μ` be a tight sequence of probability measures and `μ₀` a probability measure.
If `A` is a star sub-algebra of bounded continuous scalar functions that separates points
and the integrals of elements of `A` with respect to `μ` converge to the integrals
with respect to `μ₀`, then `μ` converges weakly to `μ₀`. -/
lemma tendsto_of_tight_of_separatesPoints (𝕜 : Type*) [RCLike 𝕜]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [PolishSpace E] [BorelSpace E]
    {ι : Type*} {𝓕 : Filter ι}
    {μ : ι → ProbabilityMeasure E} (h_tight : IsTightMeasureSet {(μ n : Measure E) | n})
    {μ₀ : ProbabilityMeasure E}
    {A : StarSubalgebra 𝕜 (E →ᵇ 𝕜)} (hA : (A.map (toContinuousMapStarₐ 𝕜)).SeparatesPoints)
    (hμ : ∀ g ∈ A, Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) 𝓕 (𝓝 (∫ x, g x ∂μ₀))) :
    Tendsto μ 𝓕 (𝓝 μ₀) := by
  obtain rfl | _ := 𝓕.eq_or_neBot
  · simp
  refine (Filter.tendsto_iff_ultrafilter _ _ _).2 fun U hU ↦ ?_
  have h_compact : IsCompact (closure {μ n | n}) :=
    isCompact_closure_of_isTightMeasureSet (by simpa using h_tight)
  obtain ⟨μ', -, hμ' : Tendsto _ _ _⟩ := h_compact.ultrafilter_le_nhds (U.map μ)
    (.trans (by simp) (monotone_principal subset_closure))
  suffices (μ' : Measure E) = μ₀ by convert hμ'; ext; rw [this]
  refine ext_of_forall_mem_subalgebra_integral_eq_of_polish hA
    fun g hg ↦ tendsto_nhds_unique ?_ ((hμ g hg).comp hU)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto 𝕜] at hμ'
  exact hμ' g

variable {ι : Type*} {𝓕 : Filter ι} {μ₀ : ProbabilityMeasure E}

set_option backward.isDefEq.respectTransparency false
omit [FiniteDimensional ℝ E] in
lemma tendsto_charPoly_of_tendsto_charFun {μ : ι → ProbabilityMeasure E}
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) 𝓕 (𝓝 (charFun μ₀ t)))
    {g : E →ᵇ ℂ} (hg : g ∈ charPoly continuous_probChar (L := innerₗ E) continuous_inner) :
    Tendsto (fun n ↦ ∫ x, g x ∂(μ n)) 𝓕 (𝓝 (∫ x, g x ∂μ₀)) := by
  rw [mem_charPoly] at hg
  obtain ⟨w, hw⟩ := hg
  have h_eq (μ : Measure E) (hμ : IsProbabilityMeasure μ) :
      ∫ x, g x ∂μ = ∑ a ∈ w.support, w a * ∫ x, (probChar (innerₗ E x a) : ℂ) ∂μ := by
    simp_rw [hw]
    rw [integral_finset_sum]
    · congr with y
      rw [integral_const_mul]
    · refine fun i hi ↦ Integrable.const_mul ?_ _
      change Integrable (innerProbChar i) μ
      exact BoundedContinuousFunction.integrable μ _
  simp_rw [h_eq (μ _), h_eq μ₀]
  refine tendsto_finset_sum _ fun y hy ↦ Tendsto.const_mul _ ?_
  simpa [← charFun_eq_integral_probChar] using h y

variable {μ : ℕ → ProbabilityMeasure E}

/-- If the characteristic functions of a sequence of probability measures converge pointwise to
the characteristic function of a probability measure, then the measures converge weakly. -/
lemma tendsto_of_tendsto_charFun
    (h : ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t))) :
    Tendsto μ atTop (𝓝 μ₀) := by
  have h_tight : IsTightMeasureSet (𝓧 := E) {μ n | n} :=
    isTightMeasureSet_of_tendsto_charFun (by fun_prop) h
  refine tendsto_of_tight_of_separatesPoints h_tight (𝕜 := ℂ)
    (A := charPoly continuous_probChar (L := innerₗ E) continuous_inner) ?_ ?_
  · refine separatesPoints_charPoly continuous_probChar probChar_ne_one _ ?_
    exact fun v hv ↦ DFunLike.ne_iff.mpr ⟨v, inner_self_ne_zero.mpr hv⟩
  · exact fun g ↦ tendsto_charPoly_of_tendsto_charFun h

/-- The **Lévy convergence theorem**: the weak convergence of probability measures is equivalent
to the pointwise convergence of their characteristic functions. -/
theorem tendsto_iff_tendsto_charFun :
    Tendsto μ atTop (𝓝 μ₀) ↔
      ∀ t : E, Tendsto (fun n ↦ charFun (μ n) t) atTop (𝓝 (charFun μ₀ t)) := by
  refine ⟨fun h t ↦ ?_, tendsto_of_tendsto_charFun⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at h
  simp_rw [charFun_eq_integral_innerProbChar]
  exact h (innerProbChar t)

end Levy
end AnalyticCombinatorics.Compatibility

/-!
# Quasi-powers and Gaussian limit laws

This file formalizes the Mathlib-supported core of Hwang's quasi-powers theorem.

Mathlib v4.29.0 has Levy's continuity theorem for characteristic functions as
`MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun`, but not a
corresponding Curtiss-style continuity theorem for moment-generating functions.
Accordingly the main limit theorem below takes a logarithmic quasi-powers expansion
on the imaginary axis, proves convergence of normalized characteristic functions,
and then applies Levy's theorem.
-/

noncomputable section

open Asymptotics Complex Filter MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace Topology

namespace AnalyticCombinatorics
namespace Ch9
namespace LimitLaws

/-- The real inner product on `R` is multiplication. -/
lemma real_inner_eq_mul (a b : ℝ) : (inner ℝ a b : ℝ) = a * b := by
  conv_lhs =>
    rw [show a = a • (1 : ℝ) by simp, show b = b • (1 : ℝ) by simp]
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  norm_num

/-- Characteristic function of a centered and scaled real random variable. -/
lemma charFun_map_center_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : AEMeasurable X P) (μ σ t : ℝ) :
    charFun (P.map fun ω => (X ω - μ) / σ) t =
      charFun (P.map X) (σ⁻¹ * t) *
        Complex.exp (((-μ) * (σ⁻¹ * t) : ℝ) * Complex.I) := by
  rw [show (fun ω => (X ω - μ) / σ) = fun ω => σ⁻¹ * (X ω - μ) by
    funext ω
    ring]
  rw [show (fun ω => σ⁻¹ * (X ω - μ)) =
      (fun x : ℝ => σ⁻¹ * x) ∘ (fun ω => X ω - μ) from rfl]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ℝ => σ⁻¹ * x)
      (P.map (fun ω => X ω - μ)))
    (hX.sub aemeasurable_const)]
  rw [charFun_map_mul]
  rw [show (fun ω => X ω - μ) = (fun x : ℝ => x + (-μ)) ∘ X by rfl]
  rw [← AEMeasurable.map_map_of_aemeasurable
    (by fun_prop : AEMeasurable (fun x : ℝ => x + (-μ)) (P.map X)) hX]
  rw [charFun_map_add_const]
  rw [real_inner_eq_mul]

/-- The real scale identity behind the quasi-powers normalization. -/
lemma quasiPower_scale_sq {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 = t ^ 2 := by
  have hsq : (Real.sqrt (β * u₂)) ^ 2 = β * u₂ := by
    rw [Real.sq_sqrt]
    positivity
  have hs_ne : (Real.sqrt (β * u₂) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (mul_pos hβ hu₂)
  field_simp [pow_two, hs_ne]
  rw [hsq]

/-- The quadratic term in the normalized quasi-powers exponent tends to the Gaussian exponent. -/
lemma quasiPower_quadratic_term {β u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂) :
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2) =
      - (t : ℂ) ^ 2 / 2 := by
  have hscale := quasiPower_scale_sq (β := β) (u₂ := u₂) (t := t) hβ hu₂
  calc
    (β : ℂ) * ((u₂ : ℂ) *
        (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 / 2)
        = - (((β * u₂ * ((Real.sqrt (β * u₂))⁻¹ * t) ^ 2 : ℝ) : ℂ)) / 2 := by
          rw [show
            (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)) ^ 2 =
              - ((((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ) ^ 2) by
            rw [pow_two]
            calc
              (Complex.I * ↑((√(β * u₂))⁻¹ * t)) *
                  (Complex.I * ↑((√(β * u₂))⁻¹ * t))
                  = (Complex.I * Complex.I) *
                      (↑((√(β * u₂))⁻¹ * t) * ↑((√(β * u₂))⁻¹ * t)) := by
                    ring
              _ = -↑((√(β * u₂))⁻¹ * t) ^ 2 := by
                    rw [Complex.I_mul_I]
                    ring]
          norm_num
          ring
    _ = - (t : ℂ) ^ 2 / 2 := by
          rw [hscale]
          norm_num

/-- The centering cancels the linear term of the quasi-powers exponent. -/
lemma quasiPower_linear_cancel {β u₁ u₂ t : ℝ} :
    (β : ℂ) *
        ((u₁ : ℂ) * (Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ))) +
      (((-(β * u₁)) * ((Real.sqrt (β * u₂))⁻¹ * t) : ℝ) : ℂ) * Complex.I = 0 := by
  norm_num
  ring

/-- The normalized quasi-powers exponent reduces to the Gaussian exponent plus remainders. -/
lemma quasiPower_exponent_eq {β u₁ u₂ t : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂)
    (r v : ℂ) :
    let z : ℂ := Complex.I * (((Real.sqrt (β * u₂))⁻¹ * t : ℝ) : ℂ)
    (β : ℂ) * ((u₁ : ℂ) * z + (u₂ : ℂ) * z ^ 2 / 2 + r) + v +
        (((-(β * u₁)) * ((Real.sqrt (β * u₂))⁻¹ * t) : ℝ) : ℂ) * Complex.I =
      - (t : ℂ) ^ 2 / 2 + (β : ℂ) * r + v := by
  dsimp
  have hlin := quasiPower_linear_cancel (β := β) (u₁ := u₁) (u₂ := u₂) (t := t)
  have hquad := quasiPower_quadratic_term (β := β) (u₂ := u₂) (t := t) hβ hu₂
  calc
    (β : ℂ) * ((u₁ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) +
          (u₂ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) ^ 2 / 2 + r) + v +
        ↑(-(β * u₁) * ((√(β * u₂))⁻¹ * t)) * I
        = ((β : ℂ) * ((u₁ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t))) +
            ↑(-(β * u₁) * ((√(β * u₂))⁻¹ * t)) * I) +
          (β : ℂ) * ((u₂ : ℂ) * (I * ↑((√(β * u₂))⁻¹ * t)) ^ 2 / 2) +
          (β : ℂ) * r + v := by
            ring
    _ = - (t : ℂ) ^ 2 / 2 + (β : ℂ) * r + v := by
          rw [hlin, hquad]
          ring

/-- If `β_n -> infinity`, then each fixed scaled real argument tends to zero. -/
lemma quasiPower_scaledRealArgument_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂) :
    Tendsto (fun n => (Real.sqrt (β n * u₂))⁻¹ * t) atTop (𝓝 0) := by
  have hprod : Tendsto (fun n => β n * u₂) atTop atTop := hβ.atTop_mul_const hu₂
  simpa using
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hprod)).mul_const t

/-- If `β_n -> infinity`, then each fixed scaled imaginary point tends to zero. -/
lemma quasiPower_scaledArgument_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂) :
    Tendsto (fun n => qpZ β u₂ n t) atTop (𝓝 0) := by
  have hreal := quasiPower_scaledRealArgument_tendsto_zero
    (β := β) (u₂ := u₂) (t := t) hβ hu₂
  simpa [qpZ] using hreal.ofReal.const_mul Complex.I

/-- A continuous analytic prefactor with value `0` at the origin is negligible after scaling. -/
lemma quasiPower_V_tendsto_zero {β : ℕ → ℝ} {u₂ t : ℝ} {V : ℂ → ℂ}
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hV : ContinuousAt V 0) (hV0 : V 0 = 0) :
    Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0) := by
  simpa [hV0] using
    hV.tendsto.comp (quasiPower_scaledArgument_tendsto_zero
      (β := β) (u₂ := u₂) (t := t) hβ hu₂)

section MomentExtraction

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β ε₁ ε₂ : ℕ → ℝ} {u₁ u₂ : ℝ}

end MomentExtraction

section QuasiPowers

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)}
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}

/-- Quasi-powers expansion on the imaginary axis implies normalized characteristic functions
converge pointwise to the standard Gaussian characteristic function. -/
theorem quasiPowers_charFun_tendsto
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0))
    (hV : ∀ t, Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0)) :
    ∀ t, Tendsto
      (fun n => charFun ((P n).map fun ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) t)
      atTop (𝓝 (Complex.exp (- (t : ℂ) ^ 2 / 2))) := by
  intro t
  obtain ⟨s₀, hs₀, hCharLocal⟩ := hChar
  have hβpos : ∀ᶠ n in atTop, 0 < β n := hβ.eventually_gt_atTop 0
  have hsmall : ∀ᶠ n in atTop, |(Real.sqrt (β n * u₂))⁻¹ * t| ≤ s₀ := by
    have htend := quasiPower_scaledRealArgument_tendsto_zero
      (β := β) (u₂ := u₂) (t := t) hβ hu₂
    filter_upwards [htend.eventually (eventually_norm_sub_lt (0 : ℝ) hs₀)] with n hn
    rw [sub_zero, Real.norm_eq_abs] at hn
    exact le_of_lt hn
  have hEq :
      (fun n =>
        charFun ((P n).map fun ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) t) =ᶠ[atTop]
        fun n => Complex.exp
          (- (t : ℂ) ^ 2 / 2 + (β n : ℂ) * R n (qpZ β u₂ n t) +
            V (qpZ β u₂ n t)) := by
    filter_upwards [hsmall, hβpos] with n hn hβn
    rw [charFun_map_center_div (hX n) (β n * u₁) (Real.sqrt (β n * u₂)) t]
    rw [hCharLocal n ((Real.sqrt (β n * u₂))⁻¹ * t) hn]
    rw [← Complex.exp_add]
    unfold qpZ
    rw [quasiPower_exponent_eq
      (β := β n) (u₁ := u₁) (u₂ := u₂) (t := t) hβn hu₂]
  have harg :
      Tendsto
        (fun n => - (t : ℂ) ^ 2 / 2 + (β n : ℂ) * R n (qpZ β u₂ n t) +
          V (qpZ β u₂ n t)) atTop
        (𝓝 (- (t : ℂ) ^ 2 / 2)) := by
    simpa [add_assoc] using (tendsto_const_nhds.add ((hR t).add (hV t)))
  exact Tendsto.congr' hEq.symm harg.cexp

variable [∀ n, IsProbabilityMeasure (P n)]

/-- The Mathlib-supported core quasi-powers theorem: characteristic-function convergence from the
logarithmic expansion implies convergence in distribution to `gaussianReal 0 1`. -/
theorem quasiPowers_tendstoInDistribution
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0))
    (hV : ∀ t, Tendsto (fun n => V (qpZ β u₂ n t)) atTop (𝓝 0)) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) where
  forall_aemeasurable n := by fun_prop
  aemeasurable_limit := by fun_prop
  tendsto := by
    refine AnalyticCombinatorics.Compatibility.tendsto_iff_tendsto_charFun.2 ?_
    intro t
    have hcf := quasiPowers_charFun_tendsto (P := P) (X := X) (β := β)
      (u₁ := u₁) (u₂ := u₂) (R := R) (V := V) hX hβ hu₂ hChar hR hV t
    simpa [charFun_gaussianReal, neg_div] using hcf

end QuasiPowers
end LimitLaws
end Ch9
end AnalyticCombinatorics
end

open AnalyticCombinatorics AnalyticCombinatorics.Ch9 AnalyticCombinatorics.Ch9.LimitLaws
open Asymptotics Complex Filter MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology
variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {P : (n : ℕ) → Measure (Ω n)}
variable {X : (n : ℕ) → Ω n → ℝ}
variable {β : ℕ → ℝ} {u₁ u₂ : ℝ} {R : ℕ → ℂ → ℂ} {V : ℂ → ℂ}
variable [∀ n, IsProbabilityMeasure (P n)]
theorem solution
    (hX : ∀ n, AEMeasurable (X n) (P n))
    (hβ : Tendsto β atTop atTop) (hu₂ : 0 < u₂)
    (hVcont : ContinuousAt V 0) (hV0 : V 0 = 0)
    (hChar : ∃ s₀ > 0, ∀ n s, |s| ≤ s₀ →
      charFun ((P n).map (X n)) s =
        Complex.exp ((β n : ℂ) * ((u₁ : ℂ) * (Complex.I * (s : ℂ)) +
          (u₂ : ℂ) * (Complex.I * (s : ℂ)) ^ 2 / 2 + R n (Complex.I * (s : ℂ))) +
          V (Complex.I * (s : ℂ))))
    (hR : ∀ t, Tendsto (fun n => (β n : ℂ) * R n (qpZ β u₂ n t)) atTop (𝓝 0)) :
    AnalyticCombinatorics.Compatibility.TendstoInDistribution
      (fun n ω => (X n ω - β n * u₁) / Real.sqrt (β n * u₂)) atTop
      (fun x : ℝ => x) P (gaussianReal 0 1) :=
  quasiPowers_tendstoInDistribution (P := P) (X := X) (β := β)
    (u₁ := u₁) (u₂ := u₂) (R := R) (V := V) hX hβ hu₂ hChar hR
    (fun t => quasiPower_V_tendsto_zero (β := β) (u₂ := u₂) (t := t)
      hβ hu₂ hVcont hV0)
