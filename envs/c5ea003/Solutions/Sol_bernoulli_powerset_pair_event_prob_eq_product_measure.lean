-- Prove2me | solution 1 for bernoulli_powerset_pair_event_prob_eq_product_measure
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T04:49:01.410189+00:00
-- url     : https://prove2.me/submissions/bb80328a-0f2c-4c8f-a6b0-41ce9c1d2739

import Theorems.Thm_bernoulli_powerset_event_prob_eq_product_measure
import Theorems.Thm_bernoulli_powerset_expectation_eq_product_measure_integral
import Definitions.Def_matrix_completion_neumann
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

/-
Pair event-probability → product-measure bridge.

`bernoulliPairEventProb p Event` is the double powerset sum
`∑_{Ω₁} ∑_{Ω₂} w(Ω₁) w(Ω₂) [Event Ω₁ Ω₂]`.  We collapse the inner sum to a
single-copy `bernoulliEventProb` and then the outer sum to a single-copy
`bernoulliExpectation`, transporting each through the already-proved keystone
bridges (`bernoulli_powerset_event_prob_eq_product_measure` 2d59092a and
`bernoulli_powerset_expectation_eq_product_measure_integral` 1526ebbb).  The
result is an integral over the first copy of the second-copy measure of the
section event; Mathlib's `Measure.prod_apply`/`measureReal` Fubini identifies it
with the genuine product-measure probability.
-/

theorem solution
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliPairEventProb (p : ℝ) Event
      = ((bernMeasure p hp).prod (bernMeasure p hp)).real
          {ω | Event (indicatorToFinset ω.1) (indicatorToFinset ω.2)} := by
  classical
  -- Step 1: collapse the inner Ω₂-sum to a single-copy event probability.
  have hinner : ∀ Ω1 : Finset (Fin n1 × Fin n2),
      (∑ Ω2 : Finset (Fin n1 × Fin n2),
          bernoulliObservationWeight (p : ℝ) Ω1 *
            bernoulliObservationWeight (p : ℝ) Ω2 *
              (if Event Ω1 Ω2 then (1 : ℝ) else 0))
        = bernoulliObservationWeight (p : ℝ) Ω1 *
            bernoulliEventProb (p : ℝ) (fun Ω2 => Event Ω1 Ω2) := by
    intro Ω1
    rw [bernoulliEventProb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro Ω2 _
    by_cases h : Event Ω1 Ω2 <;> simp [h, bernoulliObservationWeight]
  -- Rewrite the pair-event-prob as a single sum over Ω₁.
  have hpair : bernoulliPairEventProb (p : ℝ) Event
      = bernoulliExpectation (p : ℝ)
          (fun Ω1 => bernoulliEventProb (p : ℝ) (fun Ω2 => Event Ω1 Ω2)) := by
    rw [bernoulliPairEventProb, bernoulliExpectation]
    apply Finset.sum_congr rfl
    intro Ω1 _
    rw [← hinner Ω1]
  rw [hpair]
  -- Step 2: inner event-prob → second-copy measure of the section.
  have hsec : (fun Ω1 => bernoulliEventProb (p : ℝ) (fun Ω2 => Event Ω1 Ω2))
      = (fun Ω1 => (bernMeasure p hp).real
          {ω2 | Event Ω1 (indicatorToFinset ω2)}) := by
    funext Ω1
    rw [bernoulli_powerset_event_prob_eq_product_measure p hp]
  rw [hsec]
  -- Step 3: outer expectation → first-copy integral.
  rw [bernoulli_powerset_expectation_eq_product_measure_integral p hp]
  -- Step 4: Fubini for the product-measure probability of the event.
  set μ := bernMeasure p hp with hμ
  set S : Set (((Fin n1 × Fin n2) → Bool) × ((Fin n1 × Fin n2) → Bool)) :=
    {ω | Event (indicatorToFinset ω.1) (indicatorToFinset ω.2)} with hSdef
  have hSmeas : MeasurableSet S := DiscreteMeasurableSpace.forall_measurableSet _
  -- product-measure ennreal Fubini
  have hprod : (μ.prod μ) S = ∫⁻ ω1, μ {ω2 | (ω1, ω2) ∈ S} ∂μ :=
    Measure.prod_apply hSmeas
  -- section of S at ω1
  have hsection : ∀ ω1, {ω2 | (ω1, ω2) ∈ S}
      = {ω2 | Event (indicatorToFinset ω1) (indicatorToFinset ω2)} := by
    intro ω1; rfl
  -- convert measureReal integral to lintegral form
  rw [measureReal_def, hprod]
  -- ∫⁻ form: turn the real integral on the LHS into toReal of the lintegral
  have hfin : ∀ ω1, μ {ω2 | (ω1, ω2) ∈ S} ≠ ⊤ := by
    intro ω1; exact (measure_ne_top μ _)
  rw [← MeasureTheory.integral_toReal]
  · apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω1
    simp only [measureReal_def, hsection ω1]
  · -- AEMeasurable of the section measure
    refine Measurable.aemeasurable ?_
    exact measurable_measure_prodMk_left hSmeas
  · -- a.e. finiteness
    apply Filter.Eventually.of_forall
    intro ω1
    exact measure_lt_top μ _
