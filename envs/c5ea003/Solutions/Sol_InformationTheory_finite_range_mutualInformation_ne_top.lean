-- Prove2me | solution 1 for InformationTheory.finite_range_mutualInformation_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-02T04:26:30.197595+00:00
-- url     : https://prove2.me/submissions/57a78f15-3e45-4a62-8d93-181c791a600f

import Theorems.Thm_InformationTheory_klDiv_compProd_self_eq_lintegral_of_ae
import Theorems.Thm_InformationTheory_klDiv_map_measurableEmbedding
import Theorems.Thm_InformationTheory_finite_range_mutualInformation_le_marginal_entropy
import Theorems.Thm_InformationTheory_categorical_toReal_klDiv_eq_sum
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Composition.AbsolutelyContinuous

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal ProbabilityTheory

namespace InformationTheory

theorem _root_.solution
    {Omega Alpha : Type*} {mOmega : MeasurableSpace Omega}
    {mAlpha : MeasurableSpace Alpha} {k : ℕ} [NeZero k]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega → Alpha) (g : Omega → Fin k)
    (hf : Measurable f) (hg : Measurable g) :
    klDiv (mu.map (fun x ↦ (f x, g x)))
      ((mu.map f).prod (mu.map g)) ≠ ∞ := by
  let rho : Measure (Alpha × Fin k) := mu.map (fun x ↦ (f x, g x))
  let muF : Measure Alpha := mu.map f
  let kappa : Kernel Alpha (Fin k) := rho.condKernel
  let p : Measure (Fin k) := mu.map g
  letI : IsProbabilityMeasure rho := by
    dsimp [rho]
    exact Measure.isProbabilityMeasure_map (hf.prod hg).aemeasurable
  letI : IsProbabilityMeasure muF := by
    dsimp [muF]
    exact Measure.isProbabilityMeasure_map hf.aemeasurable
  letI : IsProbabilityMeasure p := by
    dsimp [p]
    exact Measure.isProbabilityMeasure_map hg.aemeasurable
  letI : IsMarkovKernel kappa := by
    dsimp [kappa]
    infer_instance
  have hfst : rho.fst = muF := by
    dsimp [rho, muF]
    exact Measure.fst_map_prodMk hg
  have hrho : muF ⊗ₘ kappa = rho := by
    rw [← hfst]
    exact rho.disintegrate rho.condKernel
  have hmarg : kappa ∘ₘ muF = p := by
    calc
      kappa ∘ₘ muF = (muF ⊗ₘ kappa).snd := by rw [Measure.snd_compProd]
      _ = rho.snd := by rw [hrho]
      _ = p := by
        dsimp [rho, p]
        exact Measure.snd_map_prodMk hf
  have hac : ∀ᵐ x ∂muF, kappa x ≪ p := by
    have hsingle (a : Fin k) (ha : p {a} = 0) :
        ∀ᵐ x ∂muF, kappa x {a} = 0 := by
      rw [← hmarg] at ha
      rw [Measure.bind_apply (MeasurableSet.singleton a) kappa.aemeasurable] at ha
      rw [lintegral_eq_zero_iff
        (Kernel.measurable_coe kappa (MeasurableSet.singleton a))] at ha
      exact ha
    have hall : ∀ᵐ x ∂muF, ∀ a : Fin k, p {a} = 0 → kappa x {a} = 0 := by
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
  have hlt : ∀ᵐ x ∂muF, klDiv (kappa x) p < ∞ := by
    filter_upwards [hac] with x hx
    exact lt_top_iff_ne_top.mpr (klDiv_ne_top hx Integrable.of_finite)
  let q : Fin k → Alpha → ℝ := fun a x ↦ (kappa x).real {a}
  have hq_meas (a : Fin k) : Measurable (q a) :=
    (Kernel.measurable_coe kappa (MeasurableSet.singleton a)).ennreal_toReal
  have hq0 (a : Fin k) (x : Alpha) : 0 ≤ q a x := by positivity
  have hq1 (a : Fin k) (x : Alpha) : q a x ≤ 1 := by
    dsimp [q]
    calc
      (kappa x).real {a} ≤ (kappa x).real Set.univ :=
        ENNReal.toReal_mono (measure_ne_top (kappa x) Set.univ)
          (measure_mono (Set.subset_univ _))
      _ = 1 := by simp
  have hq_int (a : Fin k) : Integrable (q a) muF := by
    apply Integrable.of_bound (hq_meas a).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 a x)]
      exact hq1 a x
  have hneg_int (a : Fin k) :
      Integrable (fun x ↦ Real.negMulLog (q a x)) muF := by
    apply Integrable.of_bound
      (Real.continuous_negMulLog.measurable.comp (hq_meas a)).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun x ↦ by
      change ‖Real.negMulLog (q a x)‖ ≤ 1
      rw [Real.norm_eq_abs,
        abs_of_nonneg (Real.negMulLog_nonneg (hq0 a x) (hq1 a x))]
      exact (Real.negMulLog_le_one_sub_self (hq0 a x)).trans (by linarith [hq0 a x])
  let F : Alpha → ℝ := fun x ↦
    ∑ a, (-Real.negMulLog (q a x) - q a x * Real.log (p.real {a}))
  have hF_int : Integrable F muF := by
    apply integrable_finset_sum
    intro a _
    exact (hneg_int a).neg.sub ((hq_int a).mul_const _)
  have hkl_eq : (fun x ↦ (klDiv (kappa x) p).toReal) =ᵐ[muF] F := by
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
  have hkl_ennreal : (fun x ↦ klDiv (kappa x) p) =ᵐ[muF]
      fun x ↦ ENNReal.ofReal (F x) := by
    filter_upwards [hlt, hkl_eq] with x hx heq
    calc
      klDiv (kappa x) p = ENNReal.ofReal (klDiv (kappa x) p).toReal :=
        (ENNReal.ofReal_toReal hx.ne).symm
      _ = ENNReal.ofReal (F x) := by rw [heq]
  change klDiv rho (muF.prod p) ≠ ∞
  rw [← hrho, ← Measure.compProd_const,
    klDiv_compProd_self_eq_lintegral_of_ae muF kappa (Kernel.const Alpha p)
      (by simpa using hac)]
  simp only [Kernel.const_apply]
  rw [lintegral_congr_ae hkl_ennreal]
  apply ne_of_lt
  exact lt_of_le_of_lt
    (lintegral_mono fun x ↦ Real.ofReal_le_enorm (F x))
    (hasFiniteIntegral_iff_enorm.mp hF_int.hasFiniteIntegral)



end InformationTheory

