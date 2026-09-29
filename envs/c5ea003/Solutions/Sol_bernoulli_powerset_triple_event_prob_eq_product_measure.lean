-- Prove2me | solution 1 for bernoulli_powerset_triple_event_prob_eq_product_measure
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T05:53:41.308176+00:00
-- url     : https://prove2.me/submissions/7acefeeb-98d8-4300-97f1-1b50ef9b8e48

import Theorems.Thm_bernoulli_powerset_pair_event_prob_eq_product_measure
import Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
import Definitions.Def_matrix_completion_neumann
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

/-
Triple event-probability → product-measure bridge.

Mirror of the pair bridge.  `bernoulliTripleEventProb p Event` is the triple
powerset sum.  We (1) collapse the inner Ω₂,Ω₃ double sum to a single-copy
`bernoulliPairEventProb`, (2) rewrite the whole thing as a `bernoulliExpectation`
over Ω₁, (3) transport the inner pair-event-prob through the proved pair bridge
(`bernoulli_powerset_pair_event_prob_eq_product_measure`, 97f6f327) and the outer
expectation through the integral keystone
(`bernoulli_powerset_expectation_eq_product_measure_integral`, 1526ebbb), then
(4) Fubini (`Measure.prod_apply`/`integral_toReal`) identifies the result with the
genuine 3-fold product-measure probability.
-/

theorem solution
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliTripleEventProb (p : ℝ) Event
      = ((bernMeasure p hp).prod
          ((bernMeasure p hp).prod (bernMeasure p hp))).real
          {ω | Event (indicatorToFinset ω.1)
                     (indicatorToFinset ω.2.1)
                     (indicatorToFinset ω.2.2)} := by
  classical
  -- Step 1: collapse the inner Ω₂,Ω₃ double sum to a pair-event-probability.
  have hinner : ∀ Ω1 : Finset (Fin n1 × Fin n2),
      (∑ Ω2 : Finset (Fin n1 × Fin n2), ∑ Ω3 : Finset (Fin n1 × Fin n2),
          bernoulliObservationWeight (p : ℝ) Ω1 *
            bernoulliObservationWeight (p : ℝ) Ω2 *
              bernoulliObservationWeight (p : ℝ) Ω3 *
                (if Event Ω1 Ω2 Ω3 then (1 : ℝ) else 0))
        = bernoulliObservationWeight (p : ℝ) Ω1 *
            bernoulliPairEventProb (p : ℝ) (fun Ω2 Ω3 => Event Ω1 Ω2 Ω3) := by
    intro Ω1
    rw [bernoulliPairEventProb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Ω2 _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Ω3 _
    by_cases h : Event Ω1 Ω2 Ω3 <;> simp [h] <;> ring
  -- Rewrite the triple-event-prob as a single expectation over Ω₁.
  have htriple : bernoulliTripleEventProb (p : ℝ) Event
      = bernoulliExpectation (p : ℝ)
          (fun Ω1 => bernoulliPairEventProb (p : ℝ)
            (fun Ω2 Ω3 => Event Ω1 Ω2 Ω3)) := by
    rw [bernoulliTripleEventProb, bernoulliExpectation]
    apply Finset.sum_congr rfl
    intro Ω1 _
    rw [← hinner Ω1]
  rw [htriple]
  -- Step 2: inner pair-event-prob → (μ⊗μ).real of the section.
  have hsec : (fun Ω1 => bernoulliPairEventProb (p : ℝ)
        (fun Ω2 Ω3 => Event Ω1 Ω2 Ω3))
      = (fun Ω1 => ((bernMeasure p hp).prod (bernMeasure p hp)).real
          {ω | Event Ω1 (indicatorToFinset ω.1) (indicatorToFinset ω.2)}) := by
    funext Ω1
    rw [bernoulli_powerset_pair_event_prob_eq_product_measure p hp]
  rw [hsec]
  -- Step 3: outer expectation → first-copy integral.
  rw [bernoulli_powerset_expectation_eq_product_measure_integral p hp]
  -- Step 4: Fubini for the 3-fold product-measure probability of the event.
  set μ := bernMeasure p hp with hμ
  set S : Set (((Fin n1 × Fin n2) → Bool) ×
      (((Fin n1 × Fin n2) → Bool) × ((Fin n1 × Fin n2) → Bool))) :=
    {ω | Event (indicatorToFinset ω.1)
               (indicatorToFinset ω.2.1)
               (indicatorToFinset ω.2.2)} with hSdef
  have hSmeas : MeasurableSet S := DiscreteMeasurableSpace.forall_measurableSet _
  -- product-measure ennreal Fubini: (μ ⊗ (μ⊗μ)) S = ∫⁻ ω1, (μ⊗μ){section} dμ
  have hprod : (μ.prod (μ.prod μ)) S
      = ∫⁻ ω1, (μ.prod μ) {ω23 | (ω1, ω23) ∈ S} ∂μ :=
    Measure.prod_apply hSmeas
  rw [measureReal_def, hprod]
  rw [← MeasureTheory.integral_toReal]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω1
    simp only [measureReal_def]
    rfl
  · -- AEMeasurable of the section measure
    refine Measurable.aemeasurable ?_
    exact measurable_measure_prodMk_left hSmeas
  · -- a.e. finiteness
    apply Filter.Eventually.of_forall
    intro ω1
    exact measure_lt_top (μ.prod μ) _
