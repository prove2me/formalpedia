-- Prove2me | Theorems.Thm_bernoulli_powerset_pair_event_prob_eq_product_measure
-- name    : bernoulli_powerset_pair_event_prob_eq_product_measure
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T04:48:09.239848+00:00
-- url     : https://prove2.me/theorems/712096f3-c1a0-4844-b38b-555887f8bf05
-- statement:
--   **Pair (decoupled) event-probability → Mathlib product-measure bridge.**
--
--   The decoupled matrix-completion model evaluates an event on *two independent* Bernoulli observation sets $\Omega_1,\Omega_2$ via the double powerset sum
--   $$\mathrm{bernoulliPairEventProb}\,p\,\mathrm{Event}=\sum_{\Omega_1}\sum_{\Omega_2} w(\Omega_1)\,w(\Omega_2)\,\mathbf 1[\mathrm{Event}\,\Omega_1\,\Omega_2],\qquad w(\Omega)=p^{|\Omega|}(1-p)^{N-|\Omega|}.$$
--   This theorem states that this bespoke double sum equals the genuine **Mathlib product-measure probability**
--   $$\big((\mathrm{bernMeasure}\,p)\otimes(\mathrm{bernMeasure}\,p)\big).\mathrm{real}\,\{\omega\mid \mathrm{Event}\,(\iota\,\omega_1)\,(\iota\,\omega_2)\},$$
--   where $\mathrm{bernMeasure}\,p=\mathrm{Measure.pi}$ of $\mathrm{PMF.bernoulli}\,p$ on the Bool-indicator space and $\iota=\mathrm{indicatorToFinset}$ is the indicator↔Finset bijection. It is the *pair* analogue of the single-copy bridge `bernoulli_powerset_event_prob_eq_product_measure` (2d59092a), and it unlocks Mathlib's product-measure / Fubini / independence / conditional-expectation API on the decoupled (two-copy) powerset model — the substrate needed for the de la Peña–Montgomery-Smith order-2 decoupling forward bound on `bernoulli_pair_decoupling_spectral_tail_bound_offdiag` (9aaf089d).
-- source:
--   de la Peña–Montgomery-Smith, Ann. Probab. 23 (1995) 806–816 (arXiv:math/9309211); pair analogue of the single-copy powerset→Measure.pi keystone bridge (theorem 1526ebbb / 2d59092a).

import Definitions.Def_matrix_completion_bernoulli_measure
import Definitions.Def_matrix_completion_neumann
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Prod
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem bernoulli_powerset_pair_event_prob_eq_product_measure
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Finset (Fin n1 × Fin n2) → Prop) :
    bernoulliPairEventProb (p : ℝ) Event
      = ((bernMeasure p hp).prod (bernMeasure p hp)).real
          {ω | Event (indicatorToFinset ω.1) (indicatorToFinset ω.2)} := by sorry
