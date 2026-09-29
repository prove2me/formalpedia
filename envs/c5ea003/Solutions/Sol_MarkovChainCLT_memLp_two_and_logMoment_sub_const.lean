-- Prove2me | solution 1 for MarkovChainCLT.memLp_two_and_logMoment_sub_const
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:14:58.283983+00:00
-- url     : https://prove2.me/submissions/c7c480ba-7f32-4cb2-9f24-418afc7e9874

import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.MeasureTheory.Function.L2Space

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

theorem solution {X : Type*} [MeasurableSpace X]
    (π : Measure X) [IsProbabilityMeasure π] (f : X → ℝ) (hf : Measurable f)
    (hmom : Integrable (fun x => f x ^ 2 * Real.posLog |f x|) π) (c : ℝ) :
    MemLp f 2 π ∧ Integrable (fun x => (f x - c) ^ 2 * Real.posLog |f x - c|) π := by
  have hplnn : ∀ y : ℝ, 0 ≤ Real.posLog y := fun _ => Real.posLog_nonneg
  -- measurability of the `log⁺` composites
  have hplm : Measurable (fun x => Real.posLog |f x|) := by
    simp only [Real.posLog]
    exact measurable_const.max (Real.measurable_log.comp (continuous_abs.measurable.comp hf))
  have hplm' : Measurable (fun x => Real.posLog |f x - c|) := by
    simp only [Real.posLog]
    exact measurable_const.max (Real.measurable_log.comp (continuous_abs.measurable.comp (hf.sub_const c)))
  -- (1) `log⁺|f| ≤ f² log⁺|f|`
  have hpl : ∀ x, Real.posLog |f x| ≤ f x ^ 2 * Real.posLog |f x| := by
    intro x
    rcases le_or_gt |f x| 1 with hx | hx
    · have hz : Real.posLog |f x| = 0 :=
        (Real.posLog_eq_zero_iff |f x|).mpr (by rwa [abs_abs])
      rw [hz]; simp
    · have h1 : (1:ℝ) ≤ f x ^ 2 := by nlinarith [sq_abs (f x), abs_nonneg (f x)]
      nlinarith [hplnn |f x|]
  have hplint : Integrable (fun x => Real.posLog |f x|) π := by
    refine Integrable.mono hmom hplm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hplnn _),
      abs_of_nonneg (mul_nonneg (sq_nonneg _) (hplnn _))]
    exact hpl x
  -- (2) `f² ≤ e² + f² log⁺|f|`, hence `f ∈ L²`
  have hexp2 : (Real.exp 1) ^ 2 = Real.exp 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have hsqbnd : ∀ x, f x ^ 2 ≤ Real.exp 2 + f x ^ 2 * Real.posLog |f x| := by
    intro x
    rcases le_or_gt |f x| (Real.exp 1) with hx | hx
    · have hle : f x ^ 2 ≤ Real.exp 2 := by
        rw [← sq_abs, ← hexp2]
        nlinarith [abs_nonneg (f x), Real.exp_pos 1]
      nlinarith [mul_nonneg (sq_nonneg (f x)) (hplnn |f x|)]
    · have hone : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have hge : (1:ℝ) ≤ Real.posLog |f x| := by
        rw [Real.posLog_eq_log (by rw [abs_abs]; linarith)]
        have hlog := Real.log_lt_log (Real.exp_pos 1) hx
        rw [Real.log_exp] at hlog
        exact hlog.le
      nlinarith [Real.exp_pos 2, sq_nonneg (f x)]
  have hbig : Integrable (fun x => Real.exp 2 + f x ^ 2 * Real.posLog |f x|) π :=
    (integrable_const _).add hmom
  have hsq : Integrable (fun x => f x ^ 2) π := by
    refine Integrable.mono hbig ((hf.pow_const 2).aestronglyMeasurable) ?_
    filter_upwards with x
    have hnn : (0:ℝ) ≤ Real.exp 2 + f x ^ 2 * Real.posLog |f x| := by
      nlinarith [Real.exp_pos 2, mul_nonneg (sq_nonneg (f x)) (hplnn |f x|)]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), abs_of_nonneg hnn]
    exact hsqbnd x
  refine ⟨(memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr hsq, ?_⟩
  -- (3) the log-moment survives the shift by `c`
  set L : ℝ := Real.log 2 + Real.posLog c with hLdef
  have hLnn : 0 ≤ L := by
    have h2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have := hplnn c
    simp only [hLdef]; linarith
  have hbound : ∀ x, (f x - c) ^ 2 * Real.posLog |f x - c|
      ≤ 2 * L * f x ^ 2 + 2 * (f x ^ 2 * Real.posLog |f x|)
        + 2 * L * c ^ 2 + 2 * c ^ 2 * Real.posLog |f x| := by
    intro x
    have hadd : Real.posLog (f x + -c)
        ≤ Real.log 2 + Real.posLog (f x) + Real.posLog (-c) := Real.posLog_add
    have hplsub : Real.posLog |f x - c| ≤ L + Real.posLog |f x| := by
      rw [Real.posLog_abs, Real.posLog_abs, hLdef, sub_eq_add_neg]
      rw [Real.posLog_neg] at hadd
      linarith
    have hsq2 : (f x - c) ^ 2 ≤ 2 * f x ^ 2 + 2 * c ^ 2 := by nlinarith [sq_nonneg (f x + c)]
    calc (f x - c) ^ 2 * Real.posLog |f x - c|
        ≤ (2 * f x ^ 2 + 2 * c ^ 2) * (L + Real.posLog |f x|) :=
          mul_le_mul hsq2 hplsub (hplnn _) (by nlinarith [sq_nonneg (f x), sq_nonneg c])
      _ = 2 * L * f x ^ 2 + 2 * (f x ^ 2 * Real.posLog |f x|)
            + 2 * L * c ^ 2 + 2 * c ^ 2 * Real.posLog |f x| := by ring
  have hmaj : Integrable (fun x => 2 * L * f x ^ 2 + 2 * (f x ^ 2 * Real.posLog |f x|)
      + 2 * L * c ^ 2 + 2 * c ^ 2 * Real.posLog |f x|) π :=
    (((hsq.const_mul (2 * L)).add (hmom.const_mul 2)).add
      (integrable_const (2 * L * c ^ 2))).add (hplint.const_mul (2 * c ^ 2))
  refine Integrable.mono hmaj
    ((((hf.sub_const c).pow_const 2).mul hplm').aestronglyMeasurable) ?_
  filter_upwards with x
  have hnn : (0:ℝ) ≤ 2 * L * f x ^ 2 + 2 * (f x ^ 2 * Real.posLog |f x|)
      + 2 * L * c ^ 2 + 2 * c ^ 2 * Real.posLog |f x| := by
    nlinarith [sq_nonneg (f x), sq_nonneg c, hplnn |f x|, hLnn,
      mul_nonneg (sq_nonneg (f x)) (hplnn |f x|)]
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (sq_nonneg _) (hplnn _)), abs_of_nonneg hnn]
  exact hbound x
