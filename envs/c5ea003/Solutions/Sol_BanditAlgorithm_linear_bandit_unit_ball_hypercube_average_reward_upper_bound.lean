-- Prove2me | solution 1 for BanditAlgorithm.linear_bandit_unit_ball_hypercube_average_reward_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-29T23:25:55.22436+00:00
-- url     : https://prove2.me/submissions/c04edc73-6da4-4fd6-91f2-a0ed33ec6f61

import Definitions.Def_LinearBanditProtocol
import Theorems.Thm_BanditAlgorithm_gaussian_relative_entropy_formula
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

open Real

/-- A convenient (slightly non-sharp) pointwise form of the symmetric
Kullback--Leibler lower bound. -/
theorem sq_sub_one_div_max_le_mul_log
    (x : ℝ) (hx : 0 < x) :
    (x - 1) ^ 2 / max x 1 ≤ (x - 1) * log x := by
  by_cases h : x ≤ 1
  · rw [max_eq_right h]
    have hlog := log_le_sub_one_of_pos hx
    have hmul := mul_le_mul_of_nonpos_left hlog (sub_nonpos.mpr h)
    simpa [pow_two] using hmul
  · have h1x : 1 ≤ x := le_of_lt (lt_of_not_ge h)
    rw [max_eq_left h1x]
    have hinv := log_le_sub_one_of_pos (inv_pos.mpr hx)
    rw [log_inv] at hinv
    have hlower : 1 - x⁻¹ ≤ log x := by linarith
    have hmul := mul_le_mul_of_nonneg_left hlower (sub_nonneg.mpr h1x)
    have hx0 : x ≠ 0 := ne_of_gt hx
    calc
      (x - 1) ^ 2 / x = (x - 1) * (1 - x⁻¹) := by
        field_simp
      _ ≤ (x - 1) * log x := hmul

theorem two_mul_sub_one_div_add_one_le_log
    (x : ℝ) (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ log x := by
  let f : ℝ → ℝ := fun y ↦ log y - 2 * (y - 1) / (y + 1)
  have hfcont : ContinuousOn f (Set.Ici 1) := by
    dsimp [f]
    refine (Real.continuousOn_log.mono ?_).sub ?_
    · intro y hy
      exact (lt_of_lt_of_le zero_lt_one hy).ne'
    · refine ((continuousOn_id.sub continuousOn_const).const_mul 2).div
        (continuousOn_id.add continuousOn_const) ?_
      intro y hy
      change 1 ≤ y at hy
      exact (show 0 < y + 1 by linarith).ne'
  have hfdiff : DifferentiableOn ℝ f (interior (Set.Ici 1)) := by
    rw [interior_Ici]
    dsimp [f]
    refine (Real.differentiableOn_log.mono ?_).sub ?_
    · intro y hy
      exact (lt_trans zero_lt_one hy).ne'
    · refine ((differentiableOn_id.sub (differentiableOn_const 1)).const_mul 2).div
        (differentiableOn_id.add (differentiableOn_const 1)) ?_
      intro y hy
      change 1 < y at hy
      exact (show 0 < y + 1 by linarith).ne'
  have hfderiv : ∀ y ∈ interior (Set.Ici 1), 0 ≤ deriv f y := by
    intro y hy
    rw [interior_Ici] at hy
    change 1 < y at hy
    have hy0 : y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
    have hyneg : y + 1 ≠ 0 :=
      (show 0 < y + 1 by linarith).ne'
    have hquot :
        HasDerivAt (fun z : ℝ ↦ 2 * (z - 1) / (z + 1))
          (4 / (y + 1) ^ 2) y := by
      convert ((hasDerivAt_id y).sub_const 1).const_mul 2 |>.div
        ((hasDerivAt_id y).add_const 1) hyneg using 1
      simp only [id_eq]
      field_simp
      ring
    have hd :
        HasDerivAt f
          (1 / y - 4 / (y + 1) ^ 2) y := by
      dsimp [f]
      simpa only [Pi.sub_apply, one_div] using
        (Real.hasDerivAt_log hy0).sub hquot
    rw [hd.deriv]
    have hypos : 0 < y := lt_trans zero_lt_one hy
    have hyadd : 0 < y + 1 := by linarith
    have hid : 1 / y - 4 / (y + 1) ^ 2 =
        (y - 1) ^ 2 / (y * (y + 1) ^ 2) := by
      field_simp
      ring
    rw [hid]
    positivity
  have hmono := monotoneOn_of_deriv_nonneg
    (convex_Ici 1) hfcont hfdiff hfderiv
  have h := hmono (show 1 ∈ Set.Ici (1 : ℝ) by simp)
    (show x ∈ Set.Ici (1 : ℝ) by exact hx) hx
  dsimp [f] at h
  simpa using h

theorem two_mul_sq_sub_one_div_add_one_le_mul_log
    (x : ℝ) (hx : 0 < x) :
    2 * (x - 1) ^ 2 / (x + 1) ≤ (x - 1) * log x := by
  by_cases h : 1 ≤ x
  · have hlog := two_mul_sub_one_div_add_one_le_log x h
    have hmul := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr h)
    have hxadd : x + 1 ≠ 0 := by linarith
    calc
      2 * (x - 1) ^ 2 / (x + 1) =
          (x - 1) * (2 * (x - 1) / (x + 1)) := by
        field_simp
      _ ≤ (x - 1) * log x := hmul
  · have hinv : 1 ≤ x⁻¹ := by
      exact (one_le_inv₀ hx).2 (le_of_not_ge h)
    have hlog := two_mul_sub_one_div_add_one_le_log x⁻¹ hinv
    rw [Real.log_inv] at hlog
    have hxsub : x - 1 ≤ 0 := sub_nonpos.mpr (le_of_not_ge h)
    have hrew : log x ≤ 2 * (x - 1) / (x + 1) := by
      have hx0 : x ≠ 0 := ne_of_gt hx
      field_simp [hx0] at hlog ⊢
      nlinarith
    have hmul := mul_le_mul_of_nonpos_left hrew hxsub
    have hxadd : x + 1 ≠ 0 := by linarith
    calc
      2 * (x - 1) ^ 2 / (x + 1) =
          (x - 1) * (2 * (x - 1) / (x + 1)) := by
        field_simp
      _ ≤ (x - 1) * log x := hmul

/-- Weighted Cauchy--Schwarz change of measure, using the sharp
triangular-discrimination lower bound on symmetrized KL. -/
theorem weighted_expectation_difference_sq_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPQ : P ≪ Q) (hQP : Q ≪ P)
    (g : Ω → ℝ) (hg : Measurable g)
    (hg_bound : ∀ ω, |g ω| ≤ 1)
    (hJ : Integrable (fun ω ↦
      let r := (P.rnDeriv Q ω).toReal
      (r - 1) * log r) Q) :
    (∫ ω, g ω ∂P - ∫ ω, g ω ∂Q) ^ 2 ≤
      ((∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q) *
        ((∫ ω,
          let r := (P.rnDeriv Q ω).toReal
          (r - 1) * log r ∂Q) / 2) := by
  let r : Ω → ℝ := fun ω ↦ (P.rnDeriv Q ω).toReal
  let w : Ω → ℝ := fun ω ↦ r ω + 1
  let f : Ω → ℝ := fun ω ↦ |g ω| * Real.sqrt (w ω)
  let k : Ω → ℝ := fun ω ↦ |r ω - 1| / Real.sqrt (w ω)
  have hr_meas : Measurable r := by
    exact ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv P Q)
  have hw_meas : Measurable w := hr_meas.add measurable_const
  have hf_meas : Measurable f := hg.norm.mul hw_meas.sqrt
  have hk_meas : Measurable k :=
    (hr_meas.sub measurable_const).norm.div hw_meas.sqrt
  have hr_top : ∀ᵐ ω ∂Q, P.rnDeriv Q ω < ⊤ :=
    Measure.rnDeriv_lt_top P Q
  have hr_pos_P : ∀ᵐ ω ∂P, 0 < P.rnDeriv Q ω :=
    Measure.rnDeriv_pos hPQ
  have hr_pos_Q : ∀ᵐ ω ∂Q, 0 < P.rnDeriv Q ω :=
    hQP hr_pos_P
  have hr_pos : ∀ᵐ ω ∂Q, 0 < r ω := by
    filter_upwards [hr_pos_Q, hr_top] with ω hpos htop
    exact ENNReal.toReal_pos hpos.ne' htop.ne
  have hw_pos : ∀ ω, 0 < w ω := by
    intro ω
    dsimp [w]
    exact add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  have hg2P : Integrable (fun ω ↦ g ω ^ 2) P := by
    apply Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (g ω)) zero_le_one).2 (hg_bound ω)
  have hg2Q : Integrable (fun ω ↦ g ω ^ 2) Q := by
    apply Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable 1
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (g ω)) zero_le_one).2 (hg_bound ω)
  have hrg2 : Integrable (fun ω ↦ r ω * g ω ^ 2) Q := by
    exact (integrable_toReal_rnDeriv_mul_iff hPQ).2 hg2P
  have hdom : Integrable (fun ω ↦ g ω ^ 2 * (r ω + 1)) Q := by
    simpa [mul_add, mul_comm] using hrg2.add hg2Q
  have hf_sq : Integrable (fun ω ↦ f ω ^ 2) Q := by
    refine hdom.mono' (hf_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with ω
    have hr0 : 0 ≤ r ω := ENNReal.toReal_nonneg
    have hg20 : 0 ≤ g ω ^ 2 := sq_nonneg _
    have hwle : w ω ≤ r ω + 1 := le_rfl
    have hsqrt : Real.sqrt (w ω) ^ 2 = w ω :=
      Real.sq_sqrt (le_of_lt (hw_pos ω))
    dsimp [f]
    rw [mul_pow,
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      sq_abs, hsqrt]
  have hJ' : Integrable (fun ω ↦ (r ω - 1) * log (r ω)) Q := by
    simpa only [r] using hJ
  have hJhalf : Integrable
      (fun ω ↦ ((r ω - 1) * log (r ω)) / 2) Q :=
    hJ'.div_const 2
  have hk_sq : Integrable (fun ω ↦ k ω ^ 2) Q := by
    refine hJhalf.mono' (hk_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [hr_pos] with ω hrω
    have hw0 : 0 ≤ w ω := le_of_lt (hw_pos ω)
    have hsqrt0 : Real.sqrt (w ω) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hw_pos ω))
    have hsqrt_sq : Real.sqrt (w ω) ^ 2 = w ω :=
      Real.sq_sqrt hw0
    have hpoint :=
      two_mul_sq_sub_one_div_add_one_le_mul_log (r ω) hrω
    dsimp [k]
    rw [div_pow,
      abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)),
      sq_abs, hsqrt_sq]
    dsimp [w]
    have heq :
        2 * ((r ω - 1) ^ 2 / (r ω + 1)) =
          2 * (r ω - 1) ^ 2 / (r ω + 1) := by ring
    rw [← heq] at hpoint
    nlinarith
  have hf_lp : MemLp f 2 Q :=
    (memLp_two_iff_integrable_sq hf_meas.aestronglyMeasurable).2 hf_sq
  have hk_lp : MemLp k 2 Q :=
    (memLp_two_iff_integrable_sq hk_meas.aestronglyMeasurable).2 hk_sq
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two
    (μ := Q) (f := f) (g := k)
    (Filter.Eventually.of_forall fun ω ↦ mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (Filter.Eventually.of_forall fun ω ↦ div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (by simpa using hf_lp) (by simpa using hk_lp)
  have hfk (ω : Ω) : f ω * k ω = |g ω * (r ω - 1)| := by
    have hsqrt0 : Real.sqrt (w ω) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hw_pos ω))
    dsimp [f, k]
    field_simp [hsqrt0]
    rw [abs_mul]
    ring
  have hgP : Integrable g P := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall hg_bound
  have hgQ : Integrable g Q := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall hg_bound
  have hrg : Integrable (fun ω ↦ r ω * g ω) Q :=
    (integrable_toReal_rnDeriv_mul_iff hPQ).2 hgP
  have hdiff :
      (∫ ω, g ω ∂P) - ∫ ω, g ω ∂Q =
        ∫ ω, g ω * (r ω - 1) ∂Q := by
    rw [← integral_toReal_rnDeriv_mul hPQ]
    rw [← integral_sub hrg hgQ]
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [r]
    ring
  have habs :
      |(∫ ω, g ω ∂P) - ∫ ω, g ω ∂Q| ≤
        Real.sqrt (∫ ω, f ω ^ 2 ∂Q) *
          Real.sqrt (∫ ω, k ω ^ 2 ∂Q) := by
    rw [hdiff]
    calc
      |∫ ω, g ω * (r ω - 1) ∂Q|
          ≤ ∫ ω, |g ω * (r ω - 1)| ∂Q :=
        abs_integral_le_integral_abs
      _ = ∫ ω, f ω * k ω ∂Q := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact (hfk ω).symm
      _ ≤ (∫ ω, f ω ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) *
          (∫ ω, k ω ^ (2 : ℝ) ∂Q) ^ (1 / (2 : ℝ)) := hholder
      _ = Real.sqrt (∫ ω, f ω ^ 2 ∂Q) *
          Real.sqrt (∫ ω, k ω ^ 2 ∂Q) := by
        simpa only [Real.rpow_two, Real.sqrt_eq_rpow]
  have hA0 : 0 ≤ ∫ ω, f ω ^ 2 ∂Q :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hB0 : 0 ≤ ∫ ω, k ω ^ 2 ∂Q :=
    integral_nonneg fun _ ↦ sq_nonneg _
  have hsq :
      ((∫ ω, g ω ∂P) - ∫ ω, g ω ∂Q) ^ 2 ≤
        (∫ ω, f ω ^ 2 ∂Q) * (∫ ω, k ω ^ 2 ∂Q) := by
    have hs := (sq_le_sq₀ (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).2 habs
    rw [sq_abs, mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt hB0] at hs
    exact hs
  have hf_dom : ∀ ω, f ω ^ 2 ≤ g ω ^ 2 * (r ω + 1) := by
    intro ω
    have hr0 : 0 ≤ r ω := ENNReal.toReal_nonneg
    have hg20 : 0 ≤ g ω ^ 2 := sq_nonneg _
    have hwle : w ω ≤ r ω + 1 := le_rfl
    have hsqrt : Real.sqrt (w ω) ^ 2 = w ω :=
      Real.sq_sqrt (le_of_lt (hw_pos ω))
    dsimp [f]
    rw [mul_pow, sq_abs, hsqrt]
  have hA :
      (∫ ω, f ω ^ 2 ∂Q) ≤
        (∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q := by
    calc
      (∫ ω, f ω ^ 2 ∂Q)
          ≤ ∫ ω, g ω ^ 2 * (r ω + 1) ∂Q :=
        integral_mono hf_sq hdom hf_dom
      _ = ∫ ω, (r ω * g ω ^ 2) + g ω ^ 2 ∂Q := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (∫ ω, r ω * g ω ^ 2 ∂Q) +
          ∫ ω, g ω ^ 2 ∂Q := integral_add hrg2 hg2Q
      _ = (∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q := by
        rw [integral_toReal_rnDeriv_mul hPQ]
  have hk_dom :
      ∀ᵐ ω ∂Q, k ω ^ 2 ≤
        ((r ω - 1) * log (r ω)) / 2 := by
    filter_upwards [hr_pos] with ω hrω
    have hw0 : 0 ≤ w ω := le_of_lt (hw_pos ω)
    have hsqrt_sq : Real.sqrt (w ω) ^ 2 = w ω :=
      Real.sq_sqrt hw0
    have hpoint :=
      two_mul_sq_sub_one_div_add_one_le_mul_log (r ω) hrω
    dsimp [k]
    rw [div_pow, sq_abs, hsqrt_sq]
    dsimp [w]
    have heq :
        2 * ((r ω - 1) ^ 2 / (r ω + 1)) =
          2 * (r ω - 1) ^ 2 / (r ω + 1) := by ring
    rw [← heq] at hpoint
    nlinarith
  have hB :
      (∫ ω, k ω ^ 2 ∂Q) ≤
        (∫ ω, (r ω - 1) * log (r ω) ∂Q) / 2 := by
    calc
      (∫ ω, k ω ^ 2 ∂Q) ≤
          ∫ ω, ((r ω - 1) * log (r ω)) / 2 ∂Q :=
        integral_mono_ae hk_sq hJhalf hk_dom
      _ = (∫ ω, (r ω - 1) * log (r ω) ∂Q) / 2 := by
        rw [integral_div]
  have henergy0 :
      0 ≤ (∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q := by
    exact add_nonneg (integral_nonneg fun _ ↦ sq_nonneg _)
      (integral_nonneg fun _ ↦ sq_nonneg _)
  have hJ0 : 0 ≤ ∫ ω, (r ω - 1) * log (r ω) ∂Q := by
    apply integral_nonneg_of_ae
    filter_upwards [hr_pos] with ω hrω
    have hden : 0 ≤ r ω + 1 := by linarith
    have hfrac : 0 ≤ 2 * (r ω - 1) ^ 2 / (r ω + 1) :=
      div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hden
    exact hfrac.trans
      (two_mul_sq_sub_one_div_add_one_le_mul_log (r ω) hrω)
  calc
    ((∫ ω, g ω ∂P) - ∫ ω, g ω ∂Q) ^ 2
        ≤ (∫ ω, f ω ^ 2 ∂Q) * (∫ ω, k ω ^ 2 ∂Q) := hsq
    _ ≤ ((∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q) *
        ((∫ ω, (r ω - 1) * log (r ω) ∂Q) / 2) := by
      exact mul_le_mul hA hB hB0 henergy0
    _ = ((∫ ω, g ω ^ 2 ∂P) + ∫ ω, g ω ^ 2 ∂Q) *
        ((∫ ω,
          let r := (P.rnDeriv Q ω).toReal
          (r - 1) * log r ∂Q) / 2) := by rfl

theorem integrable_jeffreys_rnDeriv_and_integral_eq
    {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hDPQ : klDiv P Q ≠ ⊤) (hDQP : klDiv Q P ≠ ⊤) :
    let r : Ω → ℝ := fun ω ↦ (P.rnDeriv Q ω).toReal
    Integrable (fun ω ↦ (r ω - 1) * log (r ω)) Q ∧
      (∫ ω, (r ω - 1) * log (r ω) ∂Q) =
        (klDiv P Q).toReal + (klDiv Q P).toReal := by
  let r : Ω → ℝ := fun ω ↦ (P.rnDeriv Q ω).toReal
  have hPQ : P ≪ Q := (klDiv_ne_top_iff.mp hDPQ).1
  have hQP : Q ≪ P := (klDiv_ne_top_iff.mp hDQP).1
  have hllrPQ : Integrable (llr P Q) P :=
    (klDiv_ne_top_iff.mp hDPQ).2
  have hllrQP : Integrable (llr Q P) Q :=
    (klDiv_ne_top_iff.mp hDQP).2
  have hrlogr : Integrable (fun ω ↦ r ω * log (r ω)) Q := by
    exact (integrable_rnDeriv_mul_log_iff hPQ).2 hllrPQ
  have hinv_P : ∀ᵐ ω ∂P,
      (P.rnDeriv Q ω)⁻¹ = Q.rnDeriv P ω :=
    Measure.inv_rnDeriv hPQ
  have hinv_Q : ∀ᵐ ω ∂Q,
      (P.rnDeriv Q ω)⁻¹ = Q.rnDeriv P ω :=
    hQP hinv_P
  have hlog_ae : (fun ω ↦ llr Q P ω) =ᵐ[Q]
      fun ω ↦ -log (r ω) := by
    filter_upwards [hinv_Q] with ω hω
    dsimp [llr, r]
    rw [← hω, ENNReal.toReal_inv, Real.log_inv]
  have hlogr : Integrable (fun ω ↦ log (r ω)) Q := by
    have hneg : Integrable (fun ω ↦ -log (r ω)) Q := by
      rwa [← integrable_congr hlog_ae]
    convert hneg.neg using 1
    funext ω
    simp
  have hJ : Integrable (fun ω ↦ (r ω - 1) * log (r ω)) Q := by
    convert hrlogr.sub hlogr using 1
    funext ω
    simp only [Pi.sub_apply]
    ring
  refine ⟨hJ, ?_⟩
  have hPQreal :
      (klDiv P Q).toReal = ∫ ω, r ω * log (r ω) ∂Q := by
    rw [toReal_klDiv_of_measure_eq hPQ (by simp)]
    exact (integral_rnDeriv_mul_log hPQ).symm
  have hQPreal :
      (klDiv Q P).toReal = ∫ ω, -log (r ω) ∂Q := by
    rw [toReal_klDiv_of_measure_eq hQP (by simp)]
    exact integral_congr_ae hlog_ae
  rw [hPQreal, hQPreal]
  change (∫ ω, (r ω - 1) * log (r ω) ∂Q) =
    (∫ ω, r ω * log (r ω) ∂Q) + ∫ ω, -log (r ω) ∂Q
  calc
    (∫ ω, (r ω - 1) * log (r ω) ∂Q) =
        ∫ ω, (r ω * log (r ω)) + (-log (r ω)) ∂Q := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, r ω * log (r ω) ∂Q) +
        ∫ ω, -log (r ω) ∂Q :=
      integral_add hrlogr hlogr.neg

end BanditAlgorithm
open MeasureTheory ProbabilityTheory InformationTheory
open Matrix

namespace BanditAlgorithm

attribute [local instance] Classical.propDecidable

private noncomputable def shiftedGaussianKernel
    {α : Type*} [MeasurableSpace α] (m : α → ℝ) (hm : Measurable m) :
    Kernel α ℝ :=
  ((Kernel.id : Kernel α α).compProd
      (Kernel.const (α × α) (gaussianReal 0 1))).map
    (fun p ↦ m p.1 + p.2)

private instance shiftedGaussianKernel.instIsMarkovKernel
    {α : Type*} [MeasurableSpace α] (m : α → ℝ) (hm : Measurable m) :
    IsMarkovKernel (shiftedGaussianKernel m hm) := by
  unfold shiftedGaussianKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

private theorem shiftedGaussianKernel_apply
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (m : α → ℝ) (hm : Measurable m)
    (a : α) :
    shiftedGaussianKernel m hm a = gaussianReal (m a) 1 := by
  rw [shiftedGaussianKernel, Kernel.map_apply]
  · rw [Kernel.compProd_apply_eq_compProd_sectR]
    simp only [Kernel.id_apply]
    have hprod :
        Measure.dirac a ⊗ₘ
            (Kernel.const (α × α) (gaussianReal 0 1)).sectR a =
          (gaussianReal 0 1).map (Prod.mk a) := by
      ext s hs
      rw [Measure.dirac_compProd_apply hs]
      rw [Kernel.sectR_apply, Kernel.const_apply,
        Measure.map_apply measurable_prodMk_left hs]
    rw [hprod]
    have hg : Measurable (fun p : α × ℝ ↦ m p.1 + p.2) :=
      (hm.comp measurable_fst).add measurable_snd
    rw [Measure.map_map hg measurable_prodMk_left]
    simpa [Function.comp_def] using
      (gaussianReal_map_const_add (μ := 0) (v := 1) (m a))
  · fun_prop

private theorem compProd_shiftedGaussianKernel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (μ : Measure α) [SFinite μ]
    (m : α → ℝ) (hm : Measurable m) :
    μ.compProd (shiftedGaussianKernel m hm) =
      (μ.compProd (Kernel.const α (gaussianReal 0 1))).map
        (fun p ↦ (p.1, m p.1 + p.2)) := by
  ext s hs
  rw [Measure.compProd_apply hs]
  rw [Measure.map_apply (by fun_prop) hs]
  rw [Measure.compProd_apply (hs.preimage (by fun_prop))]
  apply lintegral_congr
  intro a
  rw [shiftedGaussianKernel_apply m hm a]
  simp only [Kernel.const_apply]
  rw [show gaussianReal (m a) 1 =
      (gaussianReal 0 1).map (fun z ↦ m a + z) by
        simpa using (gaussianReal_map_const_add (μ := 0) (v := 1) (m a)).symm]
  rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  rfl

private noncomputable def linearStepKernel {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    Kernel (LinearBanditHistory d k) ((Fin d → ℝ) × ℝ) :=
  ((π.select k).compProd
      (Kernel.const (LinearBanditHistory d k × (Fin d → ℝ))
        (gaussianReal 0 1))).map
    (fun p ↦ (p.1, p.1 ⬝ᵥ θ + p.2))

private instance linearStepKernel.instIsMarkovKernel {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    IsMarkovKernel (linearStepKernel (k := k) θ π) := by
  unfold linearStepKernel
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

private theorem linearStepKernel_apply {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (h : LinearBanditHistory d k) :
    linearStepKernel (k := k) θ π h =
      (π.select k h).compProd
        (shiftedGaussianKernel
          (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
          (Finset.measurable_sum _ fun i _ ↦
            (measurable_pi_apply i).mul_const _)) := by
  have hrewardMap : Measurable
      (fun p : (Fin d → ℝ) × ℝ ↦ (p.1, p.1 ⬝ᵥ θ + p.2)) := by
    refine measurable_fst.prodMk ?_
    exact (Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_fst).mul_const _).add
        measurable_snd
  rw [linearStepKernel, Kernel.map_apply _ hrewardMap]
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  change ((π.select k h).compProd
      (Kernel.const (Fin d → ℝ) (gaussianReal 0 1))).map
        (fun p ↦ (p.1, p.1 ⬝ᵥ θ + p.2)) =
    (π.select k h).compProd
      (shiftedGaussianKernel
        (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
        (Finset.measurable_sum _ fun i _ ↦
          (measurable_pi_apply i).mul_const _))
  exact (compProd_shiftedGaussianKernel
    (π.select k h) (fun a : Fin d → ℝ ↦ a ⬝ᵥ θ)
      (Finset.measurable_sum _ fun i _ ↦
        (measurable_pi_apply i).mul_const _)).symm

private noncomputable def adaptiveLinearMeasure {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    (k : ℕ) → Measure (LinearBanditHistory d k)
  | 0 => Measure.dirac (fun t ↦ t.elim0)
  | k + 1 =>
      ((adaptiveLinearMeasure θ π k).compProd
        (linearStepKernel θ π)).map
          (fun p ↦ Fin.snoc p.1 p.2)

private instance adaptiveLinearMeasure.instIsProbabilityMeasure {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) (k : ℕ) :
    IsProbabilityMeasure (adaptiveLinearMeasure θ π k) := by
  induction k with
  | zero => exact Measure.dirac.isProbabilityMeasure
  | succ k ih =>
      rw [adaptiveLinearMeasure]
      haveI := ih
      exact Measure.isProbabilityMeasure_map (by fun_prop)

private theorem linearBanditMeasure_eq_adaptive {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    linearBanditMeasure θ π k = adaptiveLinearMeasure θ π k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [linearBanditMeasure, adaptiveLinearMeasure, ih]
      unfold linearStepKernel
      rw [Measure.compProd_map (by fun_prop)]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rw [← Measure.compProd_assoc']
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply Measure.map_congr
      filter_upwards [] with p
      rfl

private theorem measurable_gaussianPDF_joint
    {α : Type*} [MeasurableSpace α]
    (m : α → ℝ) (hm : Measurable m) :
    Measurable (fun p : α × ℝ ↦ gaussianPDF (m p.1) 1 p.2) := by
  unfold gaussianPDF gaussianPDFReal
  fun_prop

private theorem gaussian_withDensity_ratio (μ ν : ℝ) :
    (gaussianReal ν 1).withDensity
        (fun x ↦ gaussianPDF μ 1 x / gaussianPDF ν 1 x) =
      gaussianReal μ 1 := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    gaussianReal_of_var_ne_zero _ one_ne_zero]
  rw [← withDensity_mul]
  congr 1
  funext x
  exact ENNReal.mul_div_cancel
    (gaussianPDF_pos ν one_ne_zero x).ne'
    gaussianPDF_ne_top
  · exact measurable_gaussianPDF ν 1
  · exact (measurable_gaussianPDF μ 1).div
      (measurable_gaussianPDF ν 1)

private theorem rnDeriv_gaussian_ratio (μ ν : ℝ) :
    (gaussianReal μ 1).rnDeriv (gaussianReal ν 1) =ᵐ[gaussianReal ν 1]
      fun x ↦ gaussianPDF μ 1 x / gaussianPDF ν 1 x := by
  rw [← gaussian_withDensity_ratio μ ν]
  exact Measure.rnDeriv_withDensity _
    ((measurable_gaussianPDF μ 1).div (measurable_gaussianPDF ν 1))

private theorem gaussian_ac (μ ν : ℝ) :
    gaussianReal μ 1 ≪ gaussianReal ν 1 :=
  (gaussianReal_absolutelyContinuous μ one_ne_zero).trans
    (gaussianReal_absolutelyContinuous' ν one_ne_zero)

private noncomputable def gaussianChannelRatio
    {α : Type*} [MeasurableSpace α]
    (m m' : α → ℝ) (p : α × ℝ) : ENNReal :=
  gaussianPDF (m p.1) 1 p.2 / gaussianPDF (m' p.1) 1 p.2

private theorem measurable_gaussianChannelRatio
    {α : Type*} [MeasurableSpace α]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    Measurable (gaussianChannelRatio m m') :=
  (measurable_gaussianPDF_joint m hm).div
    (measurable_gaussianPDF_joint m' hm')

private theorem gaussianChannel_withDensity
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [SFinite ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    (ρ.compProd (shiftedGaussianKernel m' hm')).withDensity
        (gaussianChannelRatio m m') =
      ρ.compProd (shiftedGaussianKernel m hm) := by
  ext s hs
  rw [withDensity_apply _ hs]
  rw [Measure.compProd_apply hs]
  rw [← lintegral_indicator hs]
  rw [Measure.lintegral_compProd
    ((measurable_gaussianChannelRatio m m' hm hm').indicator hs)]
  apply lintegral_congr
  intro a
  rw [shiftedGaussianKernel_apply m' hm' a]
  rw [shiftedGaussianKernel_apply m hm a]
  change (∫⁻ x, s.indicator
      (fun z : α × ℝ ↦ gaussianPDF (m z.1) 1 z.2 /
        gaussianPDF (m' z.1) 1 z.2) (a, x)
      ∂gaussianReal (m' a) 1) =
    gaussianReal (m a) 1 (Prod.mk a ⁻¹' s)
  calc
    _ = ∫⁻ x in Prod.mk a ⁻¹' s,
        gaussianPDF (m a) 1 x / gaussianPDF (m' a) 1 x
        ∂gaussianReal (m' a) 1 := by
      rw [← lintegral_indicator (measurable_prodMk_left hs)]
      apply lintegral_congr
      intro x
      rfl
    _ = ((gaussianReal (m' a) 1).withDensity
          (fun x ↦ gaussianPDF (m a) 1 x /
            gaussianPDF (m' a) 1 x)) (Prod.mk a ⁻¹' s) := by
      rw [withDensity_apply _ (measurable_prodMk_left hs)]
    _ = gaussianReal (m a) 1 (Prod.mk a ⁻¹' s) := by
      rw [gaussian_withDensity_ratio]

private theorem rnDeriv_gaussianChannel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    (ρ.compProd (shiftedGaussianKernel m hm)).rnDeriv
        (ρ.compProd (shiftedGaussianKernel m' hm')) =ᵐ[
      ρ.compProd (shiftedGaussianKernel m' hm')]
        gaussianChannelRatio m m' := by
  rw [← gaussianChannel_withDensity ρ m m' hm hm']
  exact Measure.rnDeriv_withDensity _
    (measurable_gaussianChannelRatio m m' hm hm')

private theorem gaussianChannel_ac
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [SFinite ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    ρ.compProd (shiftedGaussianKernel m hm) ≪
      ρ.compProd (shiftedGaussianKernel m' hm') := by
  rw [← gaussianChannel_withDensity ρ m m' hm hm']
  exact withDensity_absolutelyContinuous _ _

private theorem klDiv_gaussianChannel
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (ρ : Measure α) [IsProbabilityMeasure ρ]
    (m m' : α → ℝ) (hm : Measurable m) (hm' : Measurable m') :
    klDiv
        (ρ.compProd (shiftedGaussianKernel m hm))
        (ρ.compProd (shiftedGaussianKernel m' hm')) =
      ∫⁻ a, ENNReal.ofReal ((m a - m' a) ^ 2 / 2) ∂ρ := by
  rw [klDiv_eq_lintegral_klFun_of_ac
    (gaussianChannel_ac ρ m m' hm hm')]
  calc
    (∫⁻ z, ENNReal.ofReal
        (klFun ((((ρ.compProd (shiftedGaussianKernel m hm)).rnDeriv
          (ρ.compProd (shiftedGaussianKernel m' hm'))) z).toReal))
        ∂ρ.compProd (shiftedGaussianKernel m' hm')) =
      ∫⁻ z, ENNReal.ofReal
        (klFun ((gaussianChannelRatio m m' z).toReal))
        ∂ρ.compProd (shiftedGaussianKernel m' hm') := by
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_gaussianChannel ρ m m' hm hm'] with z hz
      rw [hz]
    _ = ∫⁻ a, klDiv (gaussianReal (m a) 1)
        (gaussianReal (m' a) 1) ∂ρ := by
      have hmeas : Measurable (fun z : α × ℝ ↦ ENNReal.ofReal
          (klFun ((gaussianChannelRatio m m' z).toReal))) :=
        ENNReal.measurable_ofReal.comp
          (measurable_klFun.comp
            (ENNReal.measurable_toReal.comp
              (measurable_gaussianChannelRatio m m' hm hm')))
      rw [Measure.lintegral_compProd hmeas]
      apply lintegral_congr
      intro a
      rw [shiftedGaussianKernel_apply m' hm' a]
      rw [klDiv_eq_lintegral_klFun_of_ac (gaussian_ac (m a) (m' a))]
      apply lintegral_congr_ae
      filter_upwards [rnDeriv_gaussian_ratio (m a) (m' a)] with x hx
      rw [hx]
      rfl
    _ = ∫⁻ a, ENNReal.ofReal ((m a - m' a) ^ 2 / 2) ∂ρ := by
      apply lintegral_congr
      intro a
      simpa using gaussian_relative_entropy_formula (m a) (m' a)
        (v := 1) one_ne_zero

private theorem linearStepKernel_eq_gaussianStep {d k : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d) :
    linearStepKernel (k := k) θ π =
      (π.select k).compProd
        (shiftedGaussianKernel
          (fun p : LinearBanditHistory d k × (Fin d → ℝ) ↦
            p.2 ⬝ᵥ θ)
          (by
            exact Finset.measurable_sum _ fun i _ ↦
              ((measurable_pi_apply i).comp measurable_snd).mul_const _)) := by
  ext h s hs
  rw [linearStepKernel_apply θ π h]
  rw [Kernel.compProd_apply_eq_compProd_sectR]
  congr 2
  ext a t ht
  rw [Kernel.sectR_apply]
  rw [shiftedGaussianKernel_apply, shiftedGaussianKernel_apply]

private theorem klDiv_map_embedding
    {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μ η : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure η]
    {f : α → β} (hf : MeasurableEmbedding f) :
    klDiv (μ.map f) (η.map f) = klDiv μ η := by
  by_cases h_ac : μ ≪ η
  · rw [klDiv_eq_lintegral_klFun_of_ac (hf.absolutelyContinuous_map h_ac),
      klDiv_eq_lintegral_klFun_of_ac h_ac]
    rw [hf.lintegral_map]
    apply lintegral_congr_ae
    filter_upwards [hf.rnDeriv_map μ η] with x hx
    rw [hx]
  · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
    intro hmap
    apply h_ac
    intro s hηs
    have hηmap : η.map f (f '' s) = 0 := by
      rw [hf.map_apply, hf.injective.preimage_image]
      exact hηs
    have hμmap := hmap hηmap
    rw [hf.map_apply, hf.injective.preimage_image] at hμmap
    exact hμmap

private theorem klDiv_linearHistorySnoc_map {d k : ℕ}
    (μ η : Measure
      (LinearBanditHistory d k × ((Fin d → ℝ) × ℝ)))
    [IsFiniteMeasure μ] [IsFiniteMeasure η] :
    klDiv
        (μ.map (fun p :
          LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2))
        (η.map (fun p :
          LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2)) =
      klDiv μ η := by
  have hemb : MeasurableEmbedding
      (fun p : LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
        Fin.snoc
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
          p.1 p.2) := by
    apply MeasurableEmbedding.of_measurable_inverse
      (g := fun h : LinearBanditHistory d (k + 1) ↦
        (Fin.init h, h (Fin.last k)))
      (by fun_prop)
    · have hrange : Set.range
          (fun p : LinearBanditHistory d k × ((Fin d → ℝ) × ℝ) ↦
            Fin.snoc
              (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
              p.1 p.2) = Set.univ := by
        apply Set.eq_univ_of_forall
        intro h
        exact ⟨(Fin.init h, h (Fin.last k)), Fin.snoc_init_self (q := h)⟩
      rw [hrange]
      exact MeasurableSet.univ
    · fun_prop
    · intro p
      apply Prod.ext
      · exact Fin.init_snoc
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
            (n := k) (p := p.1) (x := p.2)
      · exact Fin.snoc_last
          (α := fun _ : Fin (k + 1) ↦ (Fin d → ℝ) × ℝ)
            (n := k) (p := p.1) (x := p.2)
  exact klDiv_map_embedding hemb

private theorem klDiv_sameHistory_linearStep {d k : ℕ}
    (M : Measure (LinearBanditHistory d k)) [IsProbabilityMeasure M]
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv
        (M.compProd (linearStepKernel (k := k) θ π))
        (M.compProd (linearStepKernel (k := k) θ' π)) =
      ∫⁻ p : LinearBanditHistory d k × (Fin d → ℝ),
        ENNReal.ofReal
          (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
        ∂M.compProd (π.select k) := by
  rw [linearStepKernel_eq_gaussianStep θ π,
    linearStepKernel_eq_gaussianStep θ' π]
  let m : LinearBanditHistory d k × (Fin d → ℝ) → ℝ :=
    fun p ↦ p.2 ⬝ᵥ θ
  let m' : LinearBanditHistory d k × (Fin d → ℝ) → ℝ :=
    fun p ↦ p.2 ⬝ᵥ θ'
  have hm : Measurable m := by
    exact Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_snd).mul_const _
  have hm' : Measurable m' := by
    exact Finset.measurable_sum _ fun i _ ↦
      ((measurable_pi_apply i).comp measurable_snd).mul_const _
  have hleft :
      klDiv
        ((M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m hm))).map
            MeasurableEquiv.prodAssoc.symm)
        ((M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m' hm'))).map
            MeasurableEquiv.prodAssoc.symm) =
      klDiv
        (M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m hm)))
        (M.compProd
          ((π.select k).compProd (shiftedGaussianKernel m' hm'))) :=
    klDiv_map_embedding
      (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc.symm)
  rw [Measure.compProd_assoc, Measure.compProd_assoc] at hleft
  rw [← hleft]
  simpa only [m, m'] using
    klDiv_gaussianChannel (M.compProd (π.select k)) m m' hm hm'

private theorem klDiv_adaptiveLinearMeasure_succ {d k : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (adaptiveLinearMeasure θ π (k + 1))
        (adaptiveLinearMeasure θ' π (k + 1)) =
      klDiv (adaptiveLinearMeasure θ π k)
          (adaptiveLinearMeasure θ' π k) +
        ∫⁻ p : LinearBanditHistory d k × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(adaptiveLinearMeasure θ π k).compProd (π.select k) := by
  rw [adaptiveLinearMeasure, adaptiveLinearMeasure]
  rw [klDiv_linearHistorySnoc_map]
  rw [InformationTheory.klDiv_compProd_eq_add]
  congr 1
  exact klDiv_sameHistory_linearStep
    (adaptiveLinearMeasure θ π k) θ θ' π

private theorem klDiv_adaptiveLinearMeasure_eq_sum {d n : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (adaptiveLinearMeasure θ π n)
        (adaptiveLinearMeasure θ' π n) =
      ∑ t ∈ Finset.range n,
        ∫⁻ p : LinearBanditHistory d t × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(adaptiveLinearMeasure θ π t).compProd (π.select t) := by
  induction n with
  | zero =>
      simp [adaptiveLinearMeasure]
  | succ n ih =>
      rw [klDiv_adaptiveLinearMeasure_succ, ih]
      rw [Finset.sum_range_succ]

theorem klDiv_linearBanditMeasure_eq_stage_sum {d n : ℕ}
    (θ θ' : Fin d → ℝ) (π : LinearBanditPolicy d) :
    klDiv (linearBanditMeasure θ π n)
        (linearBanditMeasure θ' π n) =
      ∑ t ∈ Finset.range n,
        ∫⁻ p : LinearBanditHistory d t × (Fin d → ℝ),
          ENNReal.ofReal
            (((p.2 ⬝ᵥ θ) - (p.2 ⬝ᵥ θ')) ^ 2 / 2)
          ∂(linearBanditMeasure θ π t).compProd (π.select t) := by
  rw [linearBanditMeasure_eq_adaptive, linearBanditMeasure_eq_adaptive]
  simpa only [← linearBanditMeasure_eq_adaptive] using
    klDiv_adaptiveLinearMeasure_eq_sum θ θ' π

private theorem measurableSet_unitBall {d : ℕ} :
    MeasurableSet {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} := by
  exact measurableSet_le
    (Finset.measurable_sum _ fun i _ ↦
      (measurable_pi_apply i).mul (measurable_pi_apply i))
    measurable_const

theorem linearBanditMeasure_allActions_unitBall {d n : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    ∀ᵐ h ∂linearBanditMeasure θ π n,
      ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1 := by
  induction n with
  | zero =>
      filter_upwards [] with h
      intro t
      exact Fin.elim0 t
  | succ n ih =>
      rw [linearBanditMeasure]
      apply (ae_map_iff
        (measurable_linearBanditHistorySnoc θ).aemeasurable
        (by
          simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun t ↦
            measurableSet_unitBall.preimage
              (measurable_fst.comp (measurable_pi_apply t)))).2
      have hpair :
          ∀ᵐ p ∂(linearBanditMeasure θ π n).compProd (π.select n),
            (∀ t, (p.1 t).1 ⬝ᵥ (p.1 t).1 ≤ 1) ∧
              p.2 ⬝ᵥ p.2 ≤ 1 := by
        apply Measure.ae_compProd_of_ae_ae
        · have hhist : MeasurableSet
              {h : LinearBanditHistory d n |
                ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1} := by
            simp only [Set.setOf_forall]
            exact MeasurableSet.iInter fun t ↦
              measurableSet_unitBall.preimage
                (measurable_fst.comp (measurable_pi_apply t))
          exact (hhist.preimage measurable_fst).inter
            (measurableSet_unitBall.preimage measurable_snd)
        · filter_upwards [ih] with h hh
          have ha : ∀ᵐ a ∂π.select n h, a ⬝ᵥ a ≤ 1 := by
            change {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} ∈ ae (π.select n h)
            rw [mem_ae_iff]
            exact hsupp n h
          filter_upwards [ha] with a ha'
          exact ⟨hh, ha'⟩
      have htriple :
          ∀ᵐ p ∂((linearBanditMeasure θ π n).compProd (π.select n)).compProd
              (Kernel.const _ (gaussianReal 0 1)),
            (∀ t, (p.1.1 t).1 ⬝ᵥ (p.1.1 t).1 ≤ 1) ∧
              p.1.2 ⬝ᵥ p.1.2 ≤ 1 := by
        have hhist : MeasurableSet
            {h : LinearBanditHistory d n |
              ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1} := by
          simp only [Set.setOf_forall]
          exact MeasurableSet.iInter fun t ↦
            measurableSet_unitBall.preimage
              (measurable_fst.comp (measurable_pi_apply t))
        have hset : MeasurableSet
            {p : LinearBanditHistory d n × (Fin d → ℝ) |
              (∀ t, (p.1 t).1 ⬝ᵥ (p.1 t).1 ≤ 1) ∧
                p.2 ⬝ᵥ p.2 ≤ 1} :=
          (hhist.preimage measurable_fst).inter
            (measurableSet_unitBall.preimage measurable_snd)
        exact Measure.ae_compProd_of_ae_fst
          (Kernel.const
            (LinearBanditHistory d n × (Fin d → ℝ))
            (gaussianReal 0 1))
          hset hpair
      filter_upwards [htriple] with p hp
      intro t
      refine Fin.lastCases ?_ (fun j ↦ ?_) t
      · simpa using hp.2
      · simpa using hp.1 j

theorem linearBanditStage_action_unitBall {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    ∀ᵐ p ∂(linearBanditMeasure θ π t).compProd (π.select t),
      p.2 ⬝ᵥ p.2 ≤ 1 := by
  apply Measure.ae_compProd_of_ae_ae
  · exact measurableSet_unitBall.preimage measurable_snd
  · filter_upwards [] with h
    have ha : {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} ∈ ae (π.select t h) := by
      rw [mem_ae_iff]
      exact hsupp t h
    exact ha

theorem coordinate_sq_le_one_of_unitBall {d : ℕ}
    (a : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) (i : Fin d) :
    a i ^ 2 ≤ 1 := by
  have hterm : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (fun j _ ↦ sq_nonneg (a j))
      (Finset.mem_univ i)
  have hsum : (∑ j, a j ^ 2) = a ⬝ᵥ a := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsum] at hterm
  exact hterm.trans ha

private theorem linearBanditSource_allActions_unitBall {d n : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    ∀ᵐ p ∂((linearBanditMeasure θ π n).compProd (π.select n)).compProd
        (Kernel.const _ (gaussianReal 0 1)),
      (∀ t, (p.1.1 t).1 ⬝ᵥ (p.1.1 t).1 ≤ 1) ∧
        p.1.2 ⬝ᵥ p.1.2 ≤ 1 := by
  have hpair :
      ∀ᵐ p ∂(linearBanditMeasure θ π n).compProd (π.select n),
        (∀ t, (p.1 t).1 ⬝ᵥ (p.1 t).1 ≤ 1) ∧
          p.2 ⬝ᵥ p.2 ≤ 1 := by
    apply Measure.ae_compProd_of_ae_ae
    · have hhist : MeasurableSet
          {h : LinearBanditHistory d n |
            ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1} := by
        simp only [Set.setOf_forall]
        exact MeasurableSet.iInter fun t ↦
          measurableSet_unitBall.preimage
            (measurable_fst.comp (measurable_pi_apply t))
      exact (hhist.preimage measurable_fst).inter
        (measurableSet_unitBall.preimage measurable_snd)
    · filter_upwards [linearBanditMeasure_allActions_unitBall θ π hsupp]
        with h hh
      have ha : ∀ᵐ a ∂π.select n h, a ⬝ᵥ a ≤ 1 := by
        change {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} ∈ ae (π.select n h)
        rw [mem_ae_iff]
        exact hsupp n h
      filter_upwards [ha] with a ha'
      exact ⟨hh, ha'⟩
  have hhist : MeasurableSet
      {h : LinearBanditHistory d n |
        ∀ t, (h t).1 ⬝ᵥ (h t).1 ≤ 1} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun t ↦
      measurableSet_unitBall.preimage
        (measurable_fst.comp (measurable_pi_apply t))
  have hset : MeasurableSet
      {p : LinearBanditHistory d n × (Fin d → ℝ) |
        (∀ t, (p.1 t).1 ⬝ᵥ (p.1 t).1 ≤ 1) ∧
          p.2 ⬝ᵥ p.2 ≤ 1} :=
    (hhist.preimage measurable_fst).inter
      (measurableSet_unitBall.preimage measurable_snd)
  exact Measure.ae_compProd_of_ae_fst
    (Kernel.const
      (LinearBanditHistory d n × (Fin d → ℝ))
      (gaussianReal 0 1))
    hset hpair

theorem linearBandit_action_sum_expectation_eq_stage_sum
    {d n : ℕ} (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (φ : ℕ → (Fin d → ℝ) → ℝ)
    (hφ : ∀ t, Measurable (φ t))
    (C : ℝ) (hC : 0 ≤ C)
    (hφC : ∀ t a, a ⬝ᵥ a ≤ 1 → |φ t a| ≤ C) :
    (∫ h, ∑ t : Fin n, φ t.1 (h t).1
      ∂linearBanditMeasure θ π n) =
      ∑ t ∈ Finset.range n,
        ∫ p, φ t p.2
          ∂(linearBanditMeasure θ π t).compProd (π.select t) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsum_meas (k : ℕ) :
          Measurable (fun h : LinearBanditHistory d k ↦
            ∑ t : Fin k, φ t.1 (h t).1) := by
        apply Finset.measurable_sum
        intro t ht
        exact (hφ t.1).comp
          (measurable_fst.comp (measurable_pi_apply t))
      have hprev_meas : Measurable
          (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
            ∑ t : Fin n, φ t.1 (p.1.1 t).1) :=
        (hsum_meas n).comp (measurable_fst.comp measurable_fst)
      have hlast_meas : Measurable
          (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
            φ n p.1.2) :=
        (hφ n).comp (measurable_snd.comp measurable_fst)
      have hsource :=
        linearBanditSource_allActions_unitBall (n := n) θ π hsupp
      have hprev_int : Integrable
          (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
            ∑ t : Fin n, φ t.1 (p.1.1 t).1)
          (((linearBanditMeasure θ π n).compProd (π.select n)).compProd
            (Kernel.const _ (gaussianReal 0 1))) := by
        apply Integrable.of_bound hprev_meas.aestronglyMeasurable (n * C)
        filter_upwards [hsource] with p hp
        rw [Real.norm_eq_abs]
        calc
          |∑ t : Fin n, φ t.1 (p.1.1 t).1|
              ≤ ∑ t : Fin n, |φ t.1 (p.1.1 t).1| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _t : Fin n, C := by
            gcongr with t
            exact hφC t.1 _ (hp.1 t)
          _ = n * C := by simp
      have hlast_int : Integrable
          (fun p : (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ ↦
            φ n p.1.2)
          (((linearBanditMeasure θ π n).compProd (π.select n)).compProd
            (Kernel.const _ (gaussianReal 0 1))) := by
        apply Integrable.of_bound hlast_meas.aestronglyMeasurable C
        filter_upwards [hsource] with p hp
        rw [Real.norm_eq_abs]
        exact hφC n _ hp.2
      rw [linearBanditMeasure]
      rw [integral_map
        (measurable_linearBanditHistorySnoc θ).aemeasurable
        (hsum_meas (n + 1)).aestronglyMeasurable]
      have hsnoc (p :
          (LinearBanditHistory d n × (Fin d → ℝ)) × ℝ) :
          (∑ t : Fin (n + 1),
                φ t.1
                ((Fin.snoc
                  (α := fun _ : Fin (n + 1) ↦ (Fin d → ℝ) × ℝ)
                  p.1.1
                  (p.1.2, p.1.2 ⬝ᵥ θ + p.2)) t).1) =
            (∑ t : Fin n, φ t.1 (p.1.1 t).1) + φ n p.1.2 := by
        rw [Fin.sum_univ_castSucc]
        congr 1
        · apply Finset.sum_congr rfl
          intro t ht
          simp
        · simp
      rw [integral_congr_ae (Filter.Eventually.of_forall hsnoc)]
      rw [integral_add hprev_int hlast_int]
      have hprev_pair : Integrable
          (fun p : LinearBanditHistory d n × (Fin d → ℝ) ↦
            ∑ t : Fin n, φ t.1 (p.1 t).1)
          ((linearBanditMeasure θ π n).compProd (π.select n)) := by
        apply Integrable.of_bound
          ((hsum_meas n).comp measurable_fst).aestronglyMeasurable
          (n * C)
        filter_upwards [linearBanditStage_action_unitBall θ π hsupp,
          Measure.ae_compProd_of_ae_fst (π.select n)
            (by
              simp only [Set.setOf_forall]
              exact MeasurableSet.iInter fun t ↦
                measurableSet_unitBall.preimage
                  (measurable_fst.comp (measurable_pi_apply t)))
            (linearBanditMeasure_allActions_unitBall θ π hsupp)]
            with p hpA hpH
        rw [Real.norm_eq_abs]
        calc
          |∑ t : Fin n, φ t.1 (p.1 t).1|
              ≤ ∑ t : Fin n, |φ t.1 (p.1 t).1| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _t : Fin n, C := by
            gcongr with t
            exact hφC t.1 _ (hpH t)
          _ = n * C := by simp
      rw [Measure.integral_compProd hprev_int,
        Measure.integral_compProd hlast_int]
      simp only [Kernel.const_apply, integral_const, probReal_univ,
        smul_eq_mul, one_mul]
      rw [Measure.integral_compProd hprev_pair]
      simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
      rw [ih]
      rw [Finset.sum_range_succ]

end BanditAlgorithm
open MeasureTheory ProbabilityTheory InformationTheory
open Matrix

namespace BanditAlgorithm

attribute [local instance] Classical.propDecidable

private def cubeSign {d : ℕ} (σ : Fin d → Bool) (i : Fin d) : ℝ :=
  if σ i then 1 else -1

private def flipCube {d : ℕ} (σ : Fin d → Bool) (i : Fin d) :
    Fin d → Bool :=
  Function.update σ i (!(σ i))

private noncomputable def cubeDelta (d n : ℕ) : ℝ :=
  Real.sqrt ((d : ℝ) / (48 * n))

private noncomputable def cubeTheta {d n : ℕ}
    (σ : Fin d → Bool) : Fin d → ℝ :=
  fun i ↦ cubeDelta d n * cubeSign σ i

private theorem cubeSign_flip_at {d : ℕ}
    (σ : Fin d → Bool) (i : Fin d) :
    cubeSign (flipCube σ i) i = -cubeSign σ i := by
  cases h : σ i <;> simp [cubeSign, flipCube, h]

private theorem cubeSign_flip_same {d : ℕ}
    (σ : Fin d → Bool) (i j : Fin d) (hji : j ≠ i) :
    cubeSign (flipCube σ i) j = cubeSign σ j := by
  simp [cubeSign, flipCube, Function.update, hji]

private theorem cubeSign_sq {d : ℕ}
    (σ : Fin d → Bool) (i : Fin d) :
    cubeSign σ i ^ 2 = 1 := by
  simp [cubeSign]

private theorem dot_cubeTheta_sub_flip {d n : ℕ}
    (σ : Fin d → Bool) (i : Fin d) (a : Fin d → ℝ) :
    a ⬝ᵥ cubeTheta (n := n) σ -
        a ⬝ᵥ cubeTheta (n := n) (flipCube σ i) =
      2 * cubeDelta d n * cubeSign σ i * a i := by
  simp only [dotProduct, cubeTheta]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ j, (a j * (cubeDelta d n * cubeSign σ j) -
      a j * (cubeDelta d n * cubeSign (flipCube σ i) j))) =
        (a i * (cubeDelta d n * cubeSign σ i) -
          a i * (cubeDelta d n * cubeSign (flipCube σ i) i)) := by
      rw [Finset.sum_eq_single i]
      · intro j hj hji
        rw [cubeSign_flip_same σ i j hji]
        ring
      · simp
    _ = 2 * cubeDelta d n * cubeSign σ i * a i := by
      rw [cubeSign_flip_at]
      ring

private theorem stage_coordinate_sq_integrable {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (i : Fin d) :
    Integrable (fun p : LinearBanditHistory d t × (Fin d → ℝ) ↦
      p.2 i ^ 2)
      ((linearBanditMeasure θ π t).compProd (π.select t)) := by
  apply Integrable.of_bound
    ((((measurable_pi_apply i).comp measurable_snd).pow_const 2).aestronglyMeasurable)
    1
  filter_upwards [linearBanditStage_action_unitBall θ π hsupp]
      with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact coordinate_sq_le_one_of_unitBall p.2 hp i

private theorem coordinate_flip_kl_eq_ofReal {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    klDiv
        (linearBanditMeasure (cubeTheta (n := n) σ) π t)
        (linearBanditMeasure
          (cubeTheta (n := n) (flipCube σ i)) π t) =
      ENNReal.ofReal
        (2 * cubeDelta d n ^ 2 *
          ∑ s ∈ Finset.range t,
            ∫ p : LinearBanditHistory d s × (Fin d → ℝ),
              p.2 i ^ 2
              ∂(linearBanditMeasure
                (cubeTheta (n := n) σ) π s).compProd (π.select s)) := by
  rw [klDiv_linearBanditMeasure_eq_stage_sum]
  have hΔ0 : 0 ≤ cubeDelta d n := by
    dsimp [cubeDelta]
    positivity
  have hterm (s : ℕ) :
      (∫⁻ p : LinearBanditHistory d s × (Fin d → ℝ),
        ENNReal.ofReal
          (((p.2 ⬝ᵥ cubeTheta (n := n) σ) -
            (p.2 ⬝ᵥ cubeTheta (n := n) (flipCube σ i))) ^ 2 / 2)
        ∂(linearBanditMeasure
          (cubeTheta (n := n) σ) π s).compProd (π.select s)) =
      ENNReal.ofReal
        (2 * cubeDelta d n ^ 2 *
          ∫ p : LinearBanditHistory d s × (Fin d → ℝ),
            p.2 i ^ 2
            ∂(linearBanditMeasure
              (cubeTheta (n := n) σ) π s).compProd (π.select s)) := by
    have hint := stage_coordinate_sq_integrable
      (t := s) (cubeTheta (n := n) σ) π hsupp i
    have hscaled : Integrable
        (fun p : LinearBanditHistory d s × (Fin d → ℝ) ↦
          2 * cubeDelta d n ^ 2 * p.2 i ^ 2)
        ((linearBanditMeasure
          (cubeTheta (n := n) σ) π s).compProd (π.select s)) :=
      hint.const_mul _
    calc
      _ = ∫⁻ p : LinearBanditHistory d s × (Fin d → ℝ),
          ENNReal.ofReal (2 * cubeDelta d n ^ 2 * p.2 i ^ 2)
          ∂(linearBanditMeasure
            (cubeTheta (n := n) σ) π s).compProd (π.select s) := by
        apply lintegral_congr
        intro p
        congr 1
        rw [dot_cubeTheta_sub_flip σ i p.2, mul_pow, mul_pow,
          cubeSign_sq]
        ring
      _ = ENNReal.ofReal
          (∫ p : LinearBanditHistory d s × (Fin d → ℝ),
            2 * cubeDelta d n ^ 2 * p.2 i ^ 2
            ∂(linearBanditMeasure
              (cubeTheta (n := n) σ) π s).compProd (π.select s)) := by
        exact (ofReal_integral_eq_lintegral_ofReal hscaled
          (Filter.Eventually.of_forall fun p ↦
            mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
              (sq_nonneg _))).symm
      _ = ENNReal.ofReal
          (2 * cubeDelta d n ^ 2 *
            ∫ p : LinearBanditHistory d s × (Fin d → ℝ),
              p.2 i ^ 2
              ∂(linearBanditMeasure
                (cubeTheta (n := n) σ) π s).compProd (π.select s)) := by
        rw [integral_const_mul]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Finset.mul_sum]
  · intro s hs
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (integral_nonneg fun _ ↦ sq_nonneg _)

private theorem flipCube_involutive {d : ℕ}
    (σ : Fin d → Bool) (i : Fin d) :
    flipCube (flipCube σ i) i = σ := by
  funext j
  by_cases hji : j = i
  · subst j
    cases h : σ i <;> simp [flipCube, h]
  · simp [flipCube, Function.update, hji]

private noncomputable def clippedCoordinate {d t : ℕ}
    (i : Fin d) (p : LinearBanditHistory d t × (Fin d → ℝ)) : ℝ :=
  max (-1) (min 1 (p.2 i))

private theorem clippedCoordinate_measurable {d t : ℕ} (i : Fin d) :
    Measurable (clippedCoordinate (t := t) i) := by
  exact measurable_const.max
    (measurable_const.min ((measurable_pi_apply i).comp measurable_snd))

private theorem abs_clippedCoordinate_le_one {d t : ℕ}
    (i : Fin d) (p : LinearBanditHistory d t × (Fin d → ℝ)) :
    |clippedCoordinate i p| ≤ 1 := by
  dsimp [clippedCoordinate]
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

private theorem clippedCoordinate_eq_of_unitBall {d t : ℕ}
    (i : Fin d) (p : LinearBanditHistory d t × (Fin d → ℝ))
    (hp : p.2 ⬝ᵥ p.2 ≤ 1) :
    clippedCoordinate i p = p.2 i := by
  have hsq := coordinate_sq_le_one_of_unitBall p.2 hp i
  have habs : |p.2 i| ≤ 1 :=
    (sq_le_one_iff_abs_le_one (p.2 i)).mp hsq
  rw [abs_le] at habs
  simp [clippedCoordinate, habs.1, habs.2]

private noncomputable def stageCoordMean {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (t : ℕ) (i : Fin d) : ℝ :=
  ∫ p : LinearBanditHistory d t × (Fin d → ℝ), p.2 i
    ∂(linearBanditMeasure θ π t).compProd (π.select t)

private noncomputable def stageCoordEnergy {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (t : ℕ) (i : Fin d) : ℝ :=
  ∫ p : LinearBanditHistory d t × (Fin d → ℝ), p.2 i ^ 2
    ∂(linearBanditMeasure θ π t).compProd (π.select t)

private noncomputable def pastCoordEnergy {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (t : ℕ) (i : Fin d) : ℝ :=
  ∑ s ∈ Finset.range t, stageCoordEnergy θ π s i

private theorem stageCoordEnergy_nonneg {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (t : ℕ) (i : Fin d) :
    0 ≤ stageCoordEnergy θ π t i :=
  integral_nonneg fun _ ↦ sq_nonneg _

private theorem pastCoordEnergy_nonneg {d : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (t : ℕ) (i : Fin d) :
    0 ≤ pastCoordEnergy θ π t i :=
  Finset.sum_nonneg fun _ _ ↦ stageCoordEnergy_nonneg θ π _ i

private theorem coordinate_pair_correlation_sq_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    ((stageCoordMean (cubeTheta (n := n) σ) π t i -
        stageCoordMean
          (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) ^ 2 ≤
      cubeDelta d n ^ 2 *
        ((stageCoordEnergy (cubeTheta (n := n) σ) π t i +
          stageCoordEnergy
            (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) *
        ((pastCoordEnergy (cubeTheta (n := n) σ) π t i +
          pastCoordEnergy
            (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) := by
  let P :=
    (linearBanditMeasure (cubeTheta (n := n) σ) π t).compProd
      (π.select t)
  let Q :=
    (linearBanditMeasure
      (cubeTheta (n := n) (flipCube σ i)) π t).compProd
      (π.select t)
  have hDPQ : klDiv P Q ≠ ⊤ := by
    dsimp [P, Q]
    rw [InformationTheory.klDiv_compProd_left]
    rw [coordinate_flip_kl_eq_ofReal π hsupp σ i]
    simp
  have hDQP : klDiv Q P ≠ ⊤ := by
    dsimp [P, Q]
    rw [InformationTheory.klDiv_compProd_left]
    have h := coordinate_flip_kl_eq_ofReal
      (n := n) (t := t) π hsupp (flipCube σ i) i
    rw [flipCube_involutive] at h
    rw [h]
    simp
  have hPQ : P ≪ Q := (klDiv_ne_top_iff.mp hDPQ).1
  have hQP : Q ≪ P := (klDiv_ne_top_iff.mp hDQP).1
  have hJeff :=
    integrable_jeffreys_rnDeriv_and_integral_eq P Q hDPQ hDQP
  have hw := weighted_expectation_difference_sq_le
    P Q hPQ hQP (clippedCoordinate (t := t) i)
      (clippedCoordinate_measurable i)
      (abs_clippedCoordinate_le_one i) hJeff.1
  rw [hJeff.2] at hw
  have hclipP : (∫ p, clippedCoordinate i p ∂P) =
      stageCoordMean (cubeTheta (n := n) σ) π t i := by
    apply integral_congr_ae
    filter_upwards [linearBanditStage_action_unitBall
      (t := t) (cubeTheta (n := n) σ) π hsupp] with p hp
    exact clippedCoordinate_eq_of_unitBall i p hp
  have hclipQ : (∫ p, clippedCoordinate i p ∂Q) =
      stageCoordMean
        (cubeTheta (n := n) (flipCube σ i)) π t i := by
    apply integral_congr_ae
    filter_upwards [linearBanditStage_action_unitBall
      (t := t) (cubeTheta (n := n) (flipCube σ i)) π hsupp] with p hp
    exact clippedCoordinate_eq_of_unitBall i p hp
  have hclip2P : (∫ p, clippedCoordinate i p ^ 2 ∂P) =
      stageCoordEnergy (cubeTheta (n := n) σ) π t i := by
    apply integral_congr_ae
    filter_upwards [linearBanditStage_action_unitBall
      (t := t) (cubeTheta (n := n) σ) π hsupp] with p hp
    rw [clippedCoordinate_eq_of_unitBall i p hp]
  have hclip2Q : (∫ p, clippedCoordinate i p ^ 2 ∂Q) =
      stageCoordEnergy
        (cubeTheta (n := n) (flipCube σ i)) π t i := by
    apply integral_congr_ae
    filter_upwards [linearBanditStage_action_unitBall
      (t := t) (cubeTheta (n := n) (flipCube σ i)) π hsupp] with p hp
    rw [clippedCoordinate_eq_of_unitBall i p hp]
  have hKLpq :
      (klDiv P Q).toReal =
        2 * cubeDelta d n ^ 2 *
          pastCoordEnergy (cubeTheta (n := n) σ) π t i := by
    dsimp [P, Q]
    rw [InformationTheory.klDiv_compProd_left]
    rw [coordinate_flip_kl_eq_ofReal π hsupp σ i,
      ENNReal.toReal_ofReal]
    · rfl
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (pastCoordEnergy_nonneg _ _ _ _)
  have hKLqp :
      (klDiv Q P).toReal =
        2 * cubeDelta d n ^ 2 *
          pastCoordEnergy
            (cubeTheta (n := n) (flipCube σ i)) π t i := by
    dsimp [P, Q]
    rw [InformationTheory.klDiv_compProd_left]
    have h := coordinate_flip_kl_eq_ofReal
      (n := n) (t := t) π hsupp (flipCube σ i) i
    rw [flipCube_involutive] at h
    rw [h, ENNReal.toReal_ofReal]
    · rfl
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
        (pastCoordEnergy_nonneg _ _ _ _)
  rw [hclipP, hclipQ, hclip2P, hclip2Q, hKLpq, hKLqp] at hw
  nlinarith [sq_nonneg
    (stageCoordMean (cubeTheta (n := n) σ) π t i -
      stageCoordMean
        (cubeTheta (n := n) (flipCube σ i)) π t i)]

private def flipCubeEquiv {d : ℕ} (i : Fin d) :
    (Fin d → Bool) ≃ (Fin d → Bool) where
  toFun σ := flipCube σ i
  invFun σ := flipCube σ i
  left_inv := fun σ ↦ flipCube_involutive σ i
  right_inv := fun σ ↦ flipCube_involutive σ i

private theorem sum_flip_neg {d : ℕ} (i : Fin d)
    (M : (Fin d → Bool) → ℝ) :
    (∑ σ, cubeSign σ i * M (flipCube σ i)) =
      -(∑ σ, cubeSign σ i * M σ) := by
  let f : (Fin d → Bool) → ℝ :=
    fun σ ↦ cubeSign σ i * M (flipCube σ i)
  calc
    (∑ σ, cubeSign σ i * M (flipCube σ i)) = ∑ σ, f σ := rfl
    _ = ∑ σ, f (flipCubeEquiv i σ) := by
      exact (Equiv.sum_comp (flipCubeEquiv i) f).symm
    _ = ∑ σ, -(cubeSign σ i * M σ) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      dsimp [f, flipCubeEquiv]
      rw [flipCube_involutive, cubeSign_flip_at]
      ring
    _ = -(∑ σ, cubeSign σ i * M σ) := by
      rw [Finset.sum_neg_distrib]

private theorem sum_sign_mean_symmetrize {d n t : ℕ}
    (π : LinearBanditPolicy d) (i : Fin d) :
    (∑ σ : Fin d → Bool,
      cubeSign σ i * stageCoordMean (cubeTheta (n := n) σ) π t i) =
      ∑ σ : Fin d → Bool,
        cubeSign σ i *
          ((stageCoordMean (cubeTheta (n := n) σ) π t i -
            stageCoordMean
              (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) := by
  have hflip := sum_flip_neg i
    (fun σ ↦ stageCoordMean (cubeTheta (n := n) σ) π t i)
  let S : ℝ := ∑ σ, cubeSign σ i *
    stageCoordMean (cubeTheta (n := n) σ) π t i
  calc
    (∑ σ, cubeSign σ i *
        stageCoordMean (cubeTheta (n := n) σ) π t i) =
        (S - (-S)) / 2 := by dsimp [S]; ring
    _ = (S -
        ∑ σ, cubeSign σ i *
          stageCoordMean
            (cubeTheta (n := n) (flipCube σ i)) π t i) / 2 := by
      rw [hflip]
    _ = ∑ σ, cubeSign σ i *
          ((stageCoordMean (cubeTheta (n := n) σ) π t i -
            stageCoordMean
              (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) := by
      dsimp [S]
      rw [← Finset.sum_sub_distrib, div_eq_mul_inv, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

private noncomputable def pairCurrentEnergy {d n : ℕ}
    (π : LinearBanditPolicy d) (t : ℕ) (i : Fin d)
    (σ : Fin d → Bool) : ℝ :=
  (stageCoordEnergy (cubeTheta (n := n) σ) π t i +
    stageCoordEnergy
      (cubeTheta (n := n) (flipCube σ i)) π t i) / 2

private noncomputable def pairPastEnergy {d n : ℕ}
    (π : LinearBanditPolicy d) (t : ℕ) (i : Fin d)
    (σ : Fin d → Bool) : ℝ :=
  (pastCoordEnergy (cubeTheta (n := n) σ) π t i +
    pastCoordEnergy
      (cubeTheta (n := n) (flipCube σ i)) π t i) / 2

private theorem pairCurrentEnergy_nonneg {d n : ℕ}
    (π : LinearBanditPolicy d) (t : ℕ) (i : Fin d)
    (σ : Fin d → Bool) :
    0 ≤ pairCurrentEnergy (n := n) π t i σ := by
  dsimp [pairCurrentEnergy]
  exact div_nonneg
    (add_nonneg (stageCoordEnergy_nonneg _ _ _ _)
      (stageCoordEnergy_nonneg _ _ _ _)) (by norm_num)

private theorem pairPastEnergy_nonneg {d n : ℕ}
    (π : LinearBanditPolicy d) (t : ℕ) (i : Fin d)
    (σ : Fin d → Bool) :
    0 ≤ pairPastEnergy (n := n) π t i σ := by
  dsimp [pairPastEnergy]
  exact div_nonneg
    (add_nonneg (pastCoordEnergy_nonneg _ _ _ _)
      (pastCoordEnergy_nonneg _ _ _ _)) (by norm_num)

private theorem signed_pair_correlation_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    cubeSign σ i *
        ((stageCoordMean (cubeTheta (n := n) σ) π t i -
          stageCoordMean
            (cubeTheta (n := n) (flipCube σ i)) π t i) / 2) ≤
      cubeDelta d n *
        Real.sqrt (pairCurrentEnergy (n := n) π t i σ) *
        Real.sqrt (pairPastEnergy (n := n) π t i σ) := by
  let x := (stageCoordMean (cubeTheta (n := n) σ) π t i -
    stageCoordMean
      (cubeTheta (n := n) (flipCube σ i)) π t i) / 2
  let y := cubeDelta d n *
    Real.sqrt (pairCurrentEnergy (n := n) π t i σ) *
    Real.sqrt (pairPastEnergy (n := n) π t i σ)
  have hx2 := coordinate_pair_correlation_sq_le
    (n := n) (t := t) π hsupp σ i
  change x ^ 2 ≤ cubeDelta d n ^ 2 *
    pairCurrentEnergy (n := n) π t i σ *
    pairPastEnergy (n := n) π t i σ at hx2
  have hy0 : 0 ≤ y := by
    dsimp [y, cubeDelta]
    positivity
  have hy2 : y ^ 2 =
      cubeDelta d n ^ 2 *
        pairCurrentEnergy (n := n) π t i σ *
        pairPastEnergy (n := n) π t i σ := by
    dsimp [y]
    rw [mul_pow, mul_pow,
      Real.sq_sqrt (pairCurrentEnergy_nonneg π t i σ),
      Real.sq_sqrt (pairPastEnergy_nonneg π t i σ)]
  have habs : |x| ≤ y := by
    rw [← sq_le_sq₀ (abs_nonneg x) hy0]
    rw [sq_abs, hy2]
    exact hx2
  calc
    cubeSign σ i * x ≤ |x| := by
      cases h : σ i <;> simp [cubeSign, h, le_abs_self, neg_le_abs]
    _ ≤ y := habs

private theorem sum_flip_eq {d : ℕ} (i : Fin d)
    (M : (Fin d → Bool) → ℝ) :
    (∑ σ, M (flipCube σ i)) = ∑ σ, M σ := by
  change (∑ σ, M (flipCubeEquiv i σ)) = ∑ σ, M σ
  exact Equiv.sum_comp (flipCubeEquiv i) M

private theorem sum_pairCurrentEnergy_eq {d n t : ℕ}
    (π : LinearBanditPolicy d) (i : Fin d) :
    (∑ σ, pairCurrentEnergy (n := n) π t i σ) =
      ∑ σ, stageCoordEnergy (cubeTheta (n := n) σ) π t i := by
  have hflip := sum_flip_eq i
    (fun σ ↦ stageCoordEnergy (cubeTheta (n := n) σ) π t i)
  dsimp [pairCurrentEnergy]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [Finset.sum_add_distrib, hflip]
  ring

private theorem sum_pairPastEnergy_eq {d n t : ℕ}
    (π : LinearBanditPolicy d) (i : Fin d) :
    (∑ σ, pairPastEnergy (n := n) π t i σ) =
      ∑ σ, pastCoordEnergy (cubeTheta (n := n) σ) π t i := by
  have hflip := sum_flip_eq i
    (fun σ ↦ pastCoordEnergy (cubeTheta (n := n) σ) π t i)
  dsimp [pairPastEnergy]
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  rw [Finset.sum_add_distrib, hflip]
  ring

private theorem sum_signed_coordinate_mean_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (i : Fin d) :
    (∑ σ : Fin d → Bool,
      cubeSign σ i *
        stageCoordMean (cubeTheta (n := n) σ) π t i) ≤
      cubeDelta d n *
        Real.sqrt (∑ σ : Fin d → Bool,
          stageCoordEnergy (cubeTheta (n := n) σ) π t i) *
        Real.sqrt (∑ σ : Fin d → Bool,
          pastCoordEnergy (cubeTheta (n := n) σ) π t i) := by
  rw [sum_sign_mean_symmetrize π i]
  calc
    (∑ σ : Fin d → Bool,
        cubeSign σ i *
          ((stageCoordMean (cubeTheta (n := n) σ) π t i -
            stageCoordMean
              (cubeTheta (n := n) (flipCube σ i)) π t i) / 2))
        ≤ ∑ σ : Fin d → Bool,
          cubeDelta d n *
            Real.sqrt (pairCurrentEnergy (n := n) π t i σ) *
            Real.sqrt (pairPastEnergy (n := n) π t i σ) := by
      exact Finset.sum_le_sum fun σ hσ ↦
        signed_pair_correlation_le π hsupp σ i
    _ = cubeDelta d n *
        (∑ σ : Fin d → Bool,
          Real.sqrt (pairCurrentEnergy (n := n) π t i σ) *
          Real.sqrt (pairPastEnergy (n := n) π t i σ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ ≤ cubeDelta d n *
        (Real.sqrt (∑ σ : Fin d → Bool,
            pairCurrentEnergy (n := n) π t i σ) *
          Real.sqrt (∑ σ : Fin d → Bool,
            pairPastEnergy (n := n) π t i σ)) := by
      apply mul_le_mul_of_nonneg_left _ (by
        dsimp [cubeDelta]
        positivity)
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt
        Finset.univ
        (fun σ : Fin d → Bool ↦
          Real.sqrt (pairCurrentEnergy (n := n) π t i σ))
        (fun σ : Fin d → Bool ↦
          Real.sqrt (pairPastEnergy (n := n) π t i σ))
      simpa only [
        Real.sq_sqrt (pairCurrentEnergy_nonneg π t i _),
        Real.sq_sqrt (pairPastEnergy_nonneg π t i _)] using hcs
    _ = cubeDelta d n *
        Real.sqrt (∑ σ : Fin d → Bool,
          stageCoordEnergy (cubeTheta (n := n) σ) π t i) *
        Real.sqrt (∑ σ : Fin d → Bool,
          pastCoordEnergy (cubeTheta (n := n) σ) π t i) := by
      rw [sum_pairCurrentEnergy_eq, sum_pairPastEnergy_eq]
      ring

private theorem sum_stageCoordEnergy_le_one {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    (∑ i : Fin d, stageCoordEnergy θ π t i) ≤ 1 := by
  let μ := (linearBanditMeasure θ π t).compProd (π.select t)
  have hint (i : Fin d) :
      Integrable
        (fun p : LinearBanditHistory d t × (Fin d → ℝ) ↦ p.2 i ^ 2)
        μ :=
    stage_coordinate_sq_integrable θ π hsupp i
  calc
    (∑ i : Fin d, stageCoordEnergy θ π t i) =
        ∫ p : LinearBanditHistory d t × (Fin d → ℝ),
          ∑ i : Fin d, p.2 i ^ 2 ∂μ := by
      rw [integral_finsetSum Finset.univ
        (fun i hi ↦ hint i)]
      rfl
    _ ≤ ∫ _p : LinearBanditHistory d t × (Fin d → ℝ), (1 : ℝ) ∂μ := by
      apply integral_mono_ae
        (integrable_finsetSum Finset.univ fun i hi ↦ hint i)
        (integrable_const 1)
      filter_upwards [linearBanditStage_action_unitBall θ π hsupp]
          with p hp
      have heq : (∑ i : Fin d, p.2 i ^ 2) = p.2 ⬝ᵥ p.2 := by
        simp only [dotProduct]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rwa [heq]
    _ = 1 := by simp [μ]

private theorem sum_pastCoordEnergy_le {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    (∑ i : Fin d, pastCoordEnergy θ π t i) ≤ t := by
  calc
    (∑ i : Fin d, pastCoordEnergy θ π t i) =
        ∑ s ∈ Finset.range t,
          ∑ i : Fin d, stageCoordEnergy θ π s i := by
      simp only [pastCoordEnergy]
      rw [Finset.sum_comm]
    _ ≤ ∑ _s ∈ Finset.range t, (1 : ℝ) := by
      gcongr with s hs
      exact sum_stageCoordEnergy_le_one θ π hsupp
    _ = t := by simp

private theorem total_stage_energy_over_cube_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
      stageCoordEnergy (cubeTheta (n := n) σ) π t i) ≤
      (Fintype.card (Fin d → Bool) : ℝ) := by
  calc
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
        stageCoordEnergy (cubeTheta (n := n) σ) π t i) =
        ∑ σ : Fin d → Bool, ∑ i : Fin d,
          stageCoordEnergy (cubeTheta (n := n) σ) π t i := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _σ : Fin d → Bool, (1 : ℝ) := by
      gcongr with σ
      exact sum_stageCoordEnergy_le_one
        (cubeTheta (n := n) σ) π hsupp
    _ = (Fintype.card (Fin d → Bool) : ℝ) := by simp

private theorem total_past_energy_over_cube_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
      pastCoordEnergy (cubeTheta (n := n) σ) π t i) ≤
      (Fintype.card (Fin d → Bool) : ℝ) * t := by
  calc
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
        pastCoordEnergy (cubeTheta (n := n) σ) π t i) =
        ∑ σ : Fin d → Bool, ∑ i : Fin d,
          pastCoordEnergy (cubeTheta (n := n) σ) π t i := by
      rw [Finset.sum_comm]
    _ ≤ ∑ _σ : Fin d → Bool, (t : ℝ) := by
      gcongr with σ
      exact sum_pastCoordEnergy_le
        (cubeTheta (n := n) σ) π hsupp
    _ = (Fintype.card (Fin d → Bool) : ℝ) * t := by simp

private theorem stage_cube_reward_le {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
      cubeSign σ i *
        stageCoordMean (cubeTheta (n := n) σ) π t i) ≤
      (Fintype.card (Fin d → Bool) : ℝ) *
        cubeDelta d n * Real.sqrt t := by
  let C : ℝ := Fintype.card (Fin d → Bool)
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have ht0 : 0 ≤ (t : ℝ) := by positivity
  calc
    (∑ i : Fin d, ∑ σ : Fin d → Bool,
        cubeSign σ i *
          stageCoordMean (cubeTheta (n := n) σ) π t i)
        ≤ ∑ i : Fin d,
          cubeDelta d n *
            Real.sqrt (∑ σ : Fin d → Bool,
              stageCoordEnergy (cubeTheta (n := n) σ) π t i) *
            Real.sqrt (∑ σ : Fin d → Bool,
              pastCoordEnergy (cubeTheta (n := n) σ) π t i) := by
      exact Finset.sum_le_sum fun i hi ↦
        sum_signed_coordinate_mean_le π hsupp i
    _ = cubeDelta d n *
        (∑ i : Fin d,
          Real.sqrt (∑ σ : Fin d → Bool,
            stageCoordEnergy (cubeTheta (n := n) σ) π t i) *
          Real.sqrt (∑ σ : Fin d → Bool,
            pastCoordEnergy (cubeTheta (n := n) σ) π t i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ cubeDelta d n *
        (Real.sqrt (∑ i : Fin d, ∑ σ : Fin d → Bool,
            stageCoordEnergy (cubeTheta (n := n) σ) π t i) *
          Real.sqrt (∑ i : Fin d, ∑ σ : Fin d → Bool,
            pastCoordEnergy (cubeTheta (n := n) σ) π t i)) := by
      apply mul_le_mul_of_nonneg_left _ (by
        dsimp [cubeDelta]
        positivity)
      have hcs := Real.sum_mul_le_sqrt_mul_sqrt
        Finset.univ
        (fun i : Fin d ↦ Real.sqrt
          (∑ σ : Fin d → Bool,
            stageCoordEnergy (cubeTheta (n := n) σ) π t i))
        (fun i : Fin d ↦ Real.sqrt
          (∑ σ : Fin d → Bool,
            pastCoordEnergy (cubeTheta (n := n) σ) π t i))
      have hstage (i : Fin d) : 0 ≤
          ∑ σ : Fin d → Bool,
            stageCoordEnergy (cubeTheta (n := n) σ) π t i :=
        Finset.sum_nonneg fun σ _ ↦ stageCoordEnergy_nonneg _ _ _ _
      have hpast (i : Fin d) : 0 ≤
          ∑ σ : Fin d → Bool,
            pastCoordEnergy (cubeTheta (n := n) σ) π t i :=
        Finset.sum_nonneg fun σ _ ↦ pastCoordEnergy_nonneg _ _ _ _
      simpa only [Real.sq_sqrt (hstage _), Real.sq_sqrt (hpast _)]
        using hcs
    _ ≤ cubeDelta d n * (Real.sqrt C * Real.sqrt (C * t)) := by
      apply mul_le_mul_of_nonneg_left _ (by
        dsimp [cubeDelta]
        positivity)
      gcongr
      · exact total_stage_energy_over_cube_le π hsupp
      · exact total_past_energy_over_cube_le π hsupp
    _ = C * cubeDelta d n * Real.sqrt t := by
      rw [Real.sqrt_mul hC0]
      calc
        cubeDelta d n *
            (Real.sqrt C * (Real.sqrt C * Real.sqrt t)) =
          (Real.sqrt C * Real.sqrt C) *
            cubeDelta d n * Real.sqrt t := by ring
        _ = C * cubeDelta d n * Real.sqrt t := by
          rw [Real.mul_self_sqrt hC0]
    _ = (Fintype.card (Fin d → Bool) : ℝ) *
        cubeDelta d n * Real.sqrt t := by rfl

private theorem abs_dot_le_l1_of_unitBall {d : ℕ}
    (a θ : Fin d → ℝ) (ha : a ⬝ᵥ a ≤ 1) :
    |a ⬝ᵥ θ| ≤ ∑ i, |θ i| := by
  calc
    |a ⬝ᵥ θ| = |∑ i, a i * θ i| := rfl
    _ ≤ ∑ i, |a i * θ i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |θ i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hsq := coordinate_sq_le_one_of_unitBall a ha i
      have hai : |a i| ≤ 1 :=
        (sq_le_one_iff_abs_le_one (a i)).mp hsq
      calc
        |a i| * |θ i| ≤ 1 * |θ i| :=
          mul_le_mul_of_nonneg_right hai (abs_nonneg _)
        _ = |θ i| := one_mul _

private theorem stage_coordinate_integrable {d t : ℕ}
    (θ : Fin d → ℝ) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (i : Fin d) :
    Integrable (fun p : LinearBanditHistory d t × (Fin d → ℝ) ↦ p.2 i)
      ((linearBanditMeasure θ π t).compProd (π.select t)) := by
  apply Integrable.of_bound
    (((measurable_pi_apply i).comp measurable_snd).aestronglyMeasurable)
    1
  filter_upwards [linearBanditStage_action_unitBall θ π hsupp]
      with p hp
  rw [Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one (p.2 i)).mp
    (coordinate_sq_le_one_of_unitBall p.2 hp i)

private theorem stage_dot_cubeTheta_eq {d n t : ℕ}
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) :
    (∫ p : LinearBanditHistory d t × (Fin d → ℝ),
        p.2 ⬝ᵥ cubeTheta (n := n) σ
        ∂(linearBanditMeasure
          (cubeTheta (n := n) σ) π t).compProd (π.select t)) =
      cubeDelta d n *
        ∑ i : Fin d, cubeSign σ i *
          stageCoordMean (cubeTheta (n := n) σ) π t i := by
  let μ := (linearBanditMeasure
    (cubeTheta (n := n) σ) π t).compProd (π.select t)
  have hint (i : Fin d) :
      Integrable
        (fun p : LinearBanditHistory d t × (Fin d → ℝ) ↦
          p.2 i * (cubeDelta d n * cubeSign σ i)) μ :=
    (stage_coordinate_integrable
      (cubeTheta (n := n) σ) π hsupp i).mul_const _
  simp only [dotProduct, cubeTheta]
  rw [integral_finsetSum Finset.univ (fun i hi ↦ hint i)]
  simp_rw [integral_mul_const]
  dsimp [stageCoordMean]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end BanditAlgorithm

open BanditAlgorithm

theorem solution {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    (∑ σ : Fin d → Bool,
        ∫ h, ∑ t, (h t).1 ⬝ᵥ
          (fun i ↦ Δ * if σ i then 1 else -1)
          ∂linearBanditMeasure
            (fun i ↦ Δ * if σ i then 1 else -1) π n) ≤
      (Fintype.card (Fin d → Bool) : ℝ) *
        (n * Δ ^ 2 * Real.sqrt n) := by
  classical
  let C : ℝ := Fintype.card (Fin d → Bool)
  let Δ : ℝ := cubeDelta d n
  have hΔ0 : 0 ≤ Δ := by
    dsimp [Δ, cubeDelta]
    positivity
  have hdecomp (σ : Fin d → Bool) :
      (∫ h, ∑ t : Fin n, (h t).1 ⬝ᵥ cubeTheta (n := n) σ
        ∂linearBanditMeasure (cubeTheta (n := n) σ) π n) =
        ∑ t ∈ Finset.range n,
          ∫ p : LinearBanditHistory d t × (Fin d → ℝ),
            p.2 ⬝ᵥ cubeTheta (n := n) σ
            ∂(linearBanditMeasure
              (cubeTheta (n := n) σ) π t).compProd (π.select t) := by
    apply linearBandit_action_sum_expectation_eq_stage_sum
      (cubeTheta (n := n) σ) π hsupp
      (fun _ a ↦ a ⬝ᵥ cubeTheta (n := n) σ)
      (fun _ ↦ Finset.measurable_sum _ fun i _ ↦
        (measurable_pi_apply i).mul_const _)
      (∑ i, |cubeTheta (n := n) σ i|)
      (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
    intro t a ha
    exact abs_dot_le_l1_of_unitBall a _ ha
  change (∑ σ : Fin d → Bool,
      ∫ h, ∑ t, (h t).1 ⬝ᵥ cubeTheta (n := n) σ
        ∂linearBanditMeasure (cubeTheta (n := n) σ) π n) ≤
    C * (n * Δ ^ 2 * Real.sqrt n)
  simp_rw [hdecomp]
  rw [Finset.sum_comm]
  calc
    (∑ t ∈ Finset.range n, ∑ σ : Fin d → Bool,
        ∫ p : LinearBanditHistory d t × (Fin d → ℝ),
          p.2 ⬝ᵥ cubeTheta (n := n) σ
          ∂(linearBanditMeasure
            (cubeTheta (n := n) σ) π t).compProd (π.select t))
        = ∑ t ∈ Finset.range n,
          Δ * (∑ i : Fin d, ∑ σ : Fin d → Bool,
            cubeSign σ i *
              stageCoordMean (cubeTheta (n := n) σ) π t i) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp_rw [stage_dot_cubeTheta_eq π hsupp]
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ ∑ t ∈ Finset.range n,
        Δ * (C * Δ * Real.sqrt t) := by
      apply Finset.sum_le_sum
      intro t ht
      exact mul_le_mul_of_nonneg_left
        (stage_cube_reward_le (n := n) π hsupp) hΔ0
    _ ≤ ∑ _t ∈ Finset.range n,
        C * (Δ ^ 2 * Real.sqrt n) := by
      apply Finset.sum_le_sum
      intro t ht
      have htn : (t : ℝ) ≤ n := by
        exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp ht))
      have hsqrt : Real.sqrt (t : ℝ) ≤ Real.sqrt n :=
        Real.sqrt_le_sqrt htn
      have hC0 : 0 ≤ C := by dsimp [C]; positivity
      have hmul := mul_le_mul_of_nonneg_left hsqrt
        (mul_nonneg hC0 (sq_nonneg Δ))
      calc
        Δ * (C * Δ * Real.sqrt t) =
            C * Δ ^ 2 * Real.sqrt t := by ring
        _ ≤ C * Δ ^ 2 * Real.sqrt n := hmul
        _ = C * (Δ ^ 2 * Real.sqrt n) := by ring
    _ = C * (n * Δ ^ 2 * Real.sqrt n) := by
      simp
      ring
