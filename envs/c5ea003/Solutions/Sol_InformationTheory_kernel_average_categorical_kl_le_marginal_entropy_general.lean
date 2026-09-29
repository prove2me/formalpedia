-- Prove2me | solution 1 for InformationTheory.kernel_average_categorical_kl_le_marginal_entropy_general
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T00:25:36.087141+00:00
-- url     : https://prove2.me/submissions/53f8b97d-174b-4924-8d07-9b18240c61f3

import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Mathlib.Probability.Kernel.Posterior
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators ProbabilityTheory

namespace InformationTheory

theorem _root_.solution {Alpha : Type} {mAlpha : MeasurableSpace Alpha}
    {k : ℕ} [NeZero k] (mu : Measure Alpha) [IsProbabilityMeasure mu]
    (kappa : Kernel Alpha (Fin k)) [IsMarkovKernel kappa] :
    ∫ x, (klDiv (kappa x) (kappa ∘ₘ mu)).toReal ∂mu ≤
      ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by
  let p : Measure (Fin k) := kappa ∘ₘ mu
  letI : IsProbabilityMeasure p := by
    dsimp [p]
    infer_instance
  let q : Fin k → Alpha → ℝ := fun a x ↦ (kappa x).real {a}
  have hq_meas (a : Fin k) : Measurable (q a) := by
    exact (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).ennreal_toReal
  have hq0 (a : Fin k) (x : Alpha) : 0 ≤ q a x := by positivity
  have hq1 (a : Fin k) (x : Alpha) : q a x ≤ 1 := by
    dsimp [q]
    calc
      (kappa x).real {a} ≤ (kappa x).real Set.univ := by
        exact ENNReal.toReal_mono (measure_ne_top (kappa x) Set.univ)
          (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  have hq_int (a : Fin k) : Integrable (q a) mu := by
    apply Integrable.of_bound (hq_meas a).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 a x)]
      exact hq1 a x
  have hneg_int (a : Fin k) : Integrable (fun x ↦ Real.negMulLog (q a x)) mu := by
    apply Integrable.of_bound
      (Real.continuous_negMulLog.measurable.comp (hq_meas a)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      change ‖Real.negMulLog (q a x)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.negMulLog_nonneg (hq0 a x) (hq1 a x))]
      exact (Real.negMulLog_le_one_sub_self (hq0 a x)).trans (by linarith [hq0 a x])
  have hq_integral (a : Fin k) : ∫ x, q a x ∂mu = p.real {a} := by
    dsimp [q, p]
    simp only [measureReal_def]
    rw [integral_toReal
      (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).aemeasurable
      (Filter.Eventually.of_forall fun x ↦ measure_lt_top (kappa x) {a})]
    rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable]
  have hac : ∀ᵐ x ∂mu, kappa x ≪ p := by
    have hsingle (a : Fin k) (ha : p {a} = 0) :
        ∀ᵐ x ∂mu, kappa x {a} = 0 := by
      dsimp [p] at ha
      rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable] at ha
      rw [lintegral_eq_zero_iff
        (Kernel.measurable_coe kappa (MeasurableSet.singleton a))] at ha
      exact ha
    have hall : ∀ᵐ x ∂mu, ∀ a : Fin k, p {a} = 0 → kappa x {a} = 0 := by
      rw [ae_all_iff]
      intro a
      by_cases ha : p {a} = 0
      · filter_upwards [hsingle a ha] with x hx
        exact fun _ ↦ hx
      · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
    filter_upwards [hall] with x hx
    apply Measure.AbsolutelyContinuous.mk
    intro s _ hs
    have hs' : p (↑s.toFinite.toFinset : Set (Fin k)) = 0 := by simpa using hs
    have hzero : ∀ a ∈ s.toFinite.toFinset, kappa x {a} = 0 := by
      intro a ha
      apply hx a
      exact measure_mono_null (Set.singleton_subset_iff.mpr ha) hs'
    rw [← Set.Finite.coe_toFinset s.toFinite, ← sum_measure_singleton]
    exact Finset.sum_eq_zero hzero
  let F : Alpha → ℝ := fun x ↦
    ∑ a, (-Real.negMulLog (q a x) - q a x * Real.log (p.real {a}))
  have hF_int : Integrable F mu := by
    apply integrable_finset_sum
    intro a _
    exact (hneg_int a).neg.sub ((hq_int a).mul_const _)
  have hkl_eq : (λ x ↦ (klDiv (kappa x) p).toReal) =ᵐ[mu] F := by
    filter_upwards [hac] with x hx
    rw [categorical_toReal_klDiv_eq_sum (kappa x) p hx]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hpa : p {a} = 0
    · have hqa_measure : kappa x {a} = 0 := hx hpa
      simp [q, measureReal_def, hpa, hqa_measure, Real.negMulLog]
    · have hpa_real : p.real {a} ≠ 0 := by
        rw [measureReal_def, ENNReal.toReal_ne_zero]
        exact ⟨hpa, measure_ne_top p {a}⟩
      by_cases hqa_real : q a x = 0
      · change q a x * Real.log (q a x / p.real {a}) =
          -Real.negMulLog (q a x) - q a x * Real.log (p.real {a})
        rw [hqa_real]
        simp only [zero_div, zero_mul, Real.negMulLog_zero, neg_zero, zero_sub]
      · rw [Real.log_div hqa_real hpa_real]
        simp only [Real.negMulLog]
        ring
  rw [integral_congr_ae hkl_eq]
  calc
    ∫ x, F x ∂mu =
        ∑ a, ∫ x, (-Real.negMulLog (q a x) - q a x * Real.log (p.real {a})) ∂mu := by
      exact integral_finset_sum Finset.univ fun a _ ↦
        (hneg_int a).neg.sub ((hq_int a).mul_const _)
    _ ≤ ∑ a, Real.negMulLog (p.real {a}) := by
      apply Finset.sum_le_sum
      intro a _
      change (∫ x, (-(fun y ↦ Real.negMulLog (q a y))) x -
        (fun y ↦ q a y * Real.log (p.real {a})) x ∂mu) ≤
          Real.negMulLog (p.real {a})
      rw [integral_sub (hneg_int a).neg ((hq_int a).mul_const _)]
      have hneg_eq :
          (∫ x, (-(fun y ↦ Real.negMulLog (q a y))) x ∂mu) =
            -(∫ x, Real.negMulLog (q a x) ∂mu) := by
        simpa only using
          (MeasureTheory.integral_neg (μ := mu)
            (f := fun x : Alpha ↦ Real.negMulLog (q a x)))
      rw [hneg_eq, integral_mul_const, hq_integral]
      have hn : 0 ≤ ∫ x, Real.negMulLog (q a x) ∂mu :=
        integral_nonneg fun x ↦ Real.negMulLog_nonneg (hq0 a x) (hq1 a x)
      change -(∫ x, Real.negMulLog (q a x) ∂mu) -
          p.real {a} * Real.log (p.real {a}) ≤
        -(p.real {a}) * Real.log (p.real {a})
      linarith
    _ = ∑ a, Real.negMulLog ((kappa ∘ₘ mu).real {a}) := by rfl

end InformationTheory

