-- Prove2me | solution 1 for BanditAlgorithm.pmStoch_expected_actionSetCount_eq_selection_mass
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T19:21:33.241285+00:00
-- url     : https://prove2.me/submissions/775cc915-5e59-4045-92c3-34d64fbfdce0

import Definitions.Def_PartialMonitoringStochastic
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BanditAlgorithm

private def pmActionSetCountReal {k n : ℕ} {𝕊 : Type*}
    (S : Finset (Fin k)) (h : PMHistory k 𝕊 n) : ℝ :=
  ∑ t, if (h t).1 ∈ S then 1 else 0

private lemma measurable_pmActionSetCountReal
    {k n : ℕ} {𝕊 : Type*} [MeasurableSpace 𝕊]
    (S : Finset (Fin k)) :
    Measurable (pmActionSetCountReal (n := n) (𝕊 := 𝕊) S) := by
  unfold pmActionSetCountReal
  apply Finset.measurable_sum
  intro t ht
  exact (measurable_of_countable
    (fun c : Fin k => if c ∈ S then (1 : ℝ) else 0)).comp
      (measurable_fst.comp (measurable_pi_apply t))

private lemma integrable_of_finite_domain
    {α : Type*} [Finite α] [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ}
    (hf : Measurable f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun x : α => ‖f x‖)
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall hC)

private lemma integral_pmStochStepKernel_actionSet
    {k d n : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (S : Finset (Fin k)) (h : PMHistory k 𝕊 n) :
    (∫ z, (if z.1 ∈ S then (1 : ℝ) else 0)
        ∂pmStochStepKernel G π u hu n h) =
      ∑ c ∈ S, (π.select n h).real {c} := by
  let f : Fin k × 𝕊 → ℝ := fun z => if z.1 ∈ S then 1 else 0
  have hf : Measurable f :=
    (measurable_of_countable
      (fun c : Fin k => if c ∈ S then (1 : ℝ) else 0)).comp measurable_fst
  have hfint : Integrable f (pmStochStepKernel G π u hu n h) :=
    integrable_of_finite_domain hf
  rw [pmStochStepKernel, ProbabilityTheory.integral_compProd hfint]
  simp only [Kernel.comap_apply]
  haveI (c : Fin k) : IsProbabilityMeasure (pmSignalMeasure G u c) :=
    pmSignalMeasure_isProbabilityMeasure G u hu c
  simp only [f]
  change (∫ c, ∫ _y : 𝕊, (if c ∈ S then (1 : ℝ) else 0)
        ∂pmSignalMeasure G u c ∂π.select n h) =
      ∑ c ∈ S, (π.select n h).real {c}
  rw [show (∫ c, ∫ _y : 𝕊, (if c ∈ S then (1 : ℝ) else 0)
        ∂pmSignalMeasure G u c ∂π.select n h) =
      ∫ c, (if c ∈ S then (1 : ℝ) else 0) ∂π.select n h by
    apply integral_congr_ae
    filter_upwards [] with c
    simp]
  simp
  rw [show (fun c : Fin k => if c ∈ S then (1 : ℝ) else 0) =
      (S : Set (Fin k)).indicator (fun _ => (1 : ℝ)) by
    funext c
    simp [Set.indicator]]
  simpa only [Pi.one_apply] using
    (integral_indicator_one (μ := π.select n h)
      (show MeasurableSet (S : Set (Fin k)) by measurability))

theorem _root_.solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [MeasurableSpace 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (π : PMPolicy k 𝕊)
    (u : Fin d → ℝ) (hu : u ∈ stdSimplex ℝ (Fin d))
    (S : Finset (Fin k)) : ∀ n : ℕ,
    (∫ h, ∑ t : Fin n, (if (h t).1 ∈ S then (1 : ℝ) else 0)
        ∂pmStochMeasure G π u hu n) =
      ∑ t ∈ Finset.range n,
        ∫ h, ∑ c ∈ S, (π.select t h).real {c}
          ∂pmStochMeasure G π u hu t := by
  classical
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      let snocFn : PMHistory k 𝕊 n × (Fin k × 𝕊) → PMHistory k 𝕊 (n + 1) :=
        fun p => Fin.snoc p.1 p.2
      let F : PMHistory k 𝕊 (n + 1) → ℝ := pmActionSetCountReal S
      have hF : Measurable F := measurable_pmActionSetCountReal S
      have hsnoc : Measurable snocFn := measurable_pmHistorySnoc
      change (∫ h, F h ∂pmStochMeasure G π u hu (n + 1)) = _
      rw [pmStochMeasure]
      rw [MeasureTheory.integral_map hsnoc.aemeasurable hF.aestronglyMeasurable]
      have hsplit : ∀ p : PMHistory k 𝕊 n × (Fin k × 𝕊),
          F (snocFn p) = pmActionSetCountReal S p.1 +
            (if p.2.1 ∈ S then 1 else 0) := by
        intro p
        unfold F snocFn pmActionSetCountReal
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
      simp_rw [hsplit]
      have hprefixMeas : Measurable
          (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
            pmActionSetCountReal S p.1) :=
        (measurable_pmActionSetCountReal S).comp measurable_fst
      have hlastMeas : Measurable
          (fun p : PMHistory k 𝕊 n × (Fin k × 𝕊) =>
            if p.2.1 ∈ S then (1 : ℝ) else 0) :=
        (measurable_of_countable
          (fun c : Fin k => if c ∈ S then (1 : ℝ) else 0)).comp
            (measurable_fst.comp measurable_snd)
      have hprefixInt := integrable_of_finite_domain (μ :=
        (pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π u hu n))
          hprefixMeas
      have hlastInt := integrable_of_finite_domain (μ :=
        (pmStochMeasure G π u hu n).compProd (pmStochStepKernel G π u hu n))
          hlastMeas
      rw [integral_add hprefixInt hlastInt]
      rw [Measure.integral_compProd hprefixInt, Measure.integral_compProd hlastInt]
      haveI (h : PMHistory k 𝕊 n) :
          IsProbabilityMeasure (pmStochStepKernel G π u hu n h) := inferInstance
      simp only [Prod.fst, Prod.snd]
      simp_rw [integral_pmStochStepKernel_actionSet G π u hu S]
      have hprefix :
          (∫ h, ∫ _z, pmActionSetCountReal S h
              ∂pmStochStepKernel G π u hu n h ∂pmStochMeasure G π u hu n) =
            ∫ h, pmActionSetCountReal S h ∂pmStochMeasure G π u hu n := by
        apply integral_congr_ae
        filter_upwards [] with h
        simp
      rw [hprefix]
      change
        (∫ h, ∑ t : Fin n, (if (h t).1 ∈ S then (1 : ℝ) else 0)
            ∂pmStochMeasure G π u hu n) +
          (∫ h, ∑ c ∈ S, (π.select n h).real {c}
            ∂pmStochMeasure G π u hu n) = _
      rw [ih, Finset.sum_range_succ]

end BanditAlgorithm
