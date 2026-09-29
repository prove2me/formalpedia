-- Prove2me | Theorems.Thm_bernoulli_powerset_triple_event_prob_eq_product_measure
-- name    : bernoulli_powerset_triple_event_prob_eq_product_measure
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T05:53:18.795925+00:00
-- url     : https://prove2.me/theorems/95951356-4d47-4c73-8600-85912e913cb2
-- statement:
--   The triple (three independent copies) Bernoulli powerset event-probability equals the genuine Mathlib product-measure probability of the corresponding event on the 3-fold product $\mu\otimes(\mu\otimes\mu)$, where $\mu=\mathrm{bernMeasure}\,p$. This is the 3-fold analogue of the proved pair bridge (97f6f327) and single-copy bridge (1526ebbb/2d59092a): it transports the bespoke powerset triple-sum to a stock product measure, the substrate needed for de la Peña–Montgomery-Smith 1995 (arXiv:math/9309211) §4 Lemma 1 (the 3-copy desymmetrization triangle), which lives on a three-fold product measure.
-- source:
--   de la Peña–Montgomery-Smith, "Decoupling inequalities for the tail probabilities of multivariate U-statistics", Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211), §4 (Lemma 1, three i.i.d. copies). Measure-theoretic Fubini bridge; mirror of the proved pair bridge bernoulli_powerset_pair_event_prob_eq_product_measure.

import Definitions.Def_matrix_completion_bernoulli_measure
import Definitions.Def_matrix_completion_neumann
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem bernoulli_powerset_triple_event_prob_eq_product_measure
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) →
      Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliTripleEventProb (p : ℝ) Event
      = ((bernMeasure p hp).prod
          ((bernMeasure p hp).prod (bernMeasure p hp))).real
          {ω | Event (indicatorToFinset ω.1)
                     (indicatorToFinset ω.2.1)
                     (indicatorToFinset ω.2.2)} := by sorry
