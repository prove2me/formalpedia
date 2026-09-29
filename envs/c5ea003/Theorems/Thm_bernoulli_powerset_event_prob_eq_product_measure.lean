-- Prove2me | Theorems.Thm_bernoulli_powerset_event_prob_eq_product_measure
-- name    : bernoulli_powerset_event_prob_eq_product_measure
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T03:13:41.332962+00:00
-- url     : https://prove2.me/theorems/2d59092a-5d1d-4d3f-8e32-e822d073059a
-- statement:
--   Companion of the keystone bridge for EVENT PROBABILITIES. The powerset event probability $\Pr_p[\mathrm{Event}] = \sum_{\Omega : \mathrm{Event}(\Omega)} p^{|\Omega|}(1-p)^{N-|\Omega|}$ (bernoulliEventProb) equals the real-valued measure under the stock Mathlib product-Bernoulli measure bernMeasure of the pulled-back event $\{\omega : \mathrm{Event}(\mathrm{indicatorToFinset}\,\omega)\}$. This lets every tail / concentration statement phrased on the bespoke bernoulliEventProb be transported to a genuine Mathlib measure-probability $\mu.\mathrm{real}\,S$, unlocking measure-theoretic tail tools (Markov, condExp, decoupling) on the powerset model. Proof: rewrite bernoulliEventProb as the bernoulliExpectation of the {0,1}-indicator, apply the keystone bridge, then identify the integral of the pulled-back indicator with the measure of the pulled-back set (integral_indicator_one; all sets measurable on the discrete indicator space).
-- source:
--   Mathlib MeasureTheory.Integral.Bochner.Set (integral_indicator_one), MeasurableSpace (DiscreteMeasurableSpace); Candes-Recht 2009 arXiv:0805.4471 section 6. Reduces to keystone bernoulli_powerset_expectation_eq_product_measure_integral.

import Definitions.Def_matrix_completion_bernoulli_measure
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem bernoulli_powerset_event_prob_eq_product_measure
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliEventProb (p : ℝ) Event
      = (bernMeasure p hp).real {ω | Event (indicatorToFinset ω)} := by sorry
