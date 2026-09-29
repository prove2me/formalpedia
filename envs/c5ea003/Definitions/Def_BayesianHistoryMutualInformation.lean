-- Prove2me | Definitions.Def_BayesianHistoryMutualInformation
-- name    : BayesianHistoryMutualInformation
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-01T23:44:02.045667+00:00
-- url     : https://prove2.me/theorems/6dc560ad-d4dd-4404-98fc-d306c454970e
-- title:
--   Mutual information between bandit history and the optimal action
-- statement:
--   For a Bayesian adversarial bandit, let $H_t$ be the observed action–reward history before round $t$, and let $A^*$ be the action maximizing total reward. Define
--
--   $$
--   I_t = I(H_t;A^*) = D\!\left(P_{(H_t,A^*)}\,\middle\|\,P_{H_t}\otimes P_{A^*}\right).
--   $$
--
--   The definition uses the terminal joint law of the reward matrix and the complete history, then maps it to the required marginals.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed pp. 469–471 (PDF pp. 478–480), Theorems 36.5–36.6 and Lemma 36.7: information gained about the optimal action by the observed history.

import Definitions.Def_ThompsonSampling
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
Lattimore--Szepesvari, *Bandit Algorithms* (CUP 2020), Chapter 36,
printed pp. 469--471.  The information-gain process in Theorems 36.5--36.6
is the mutual information between the optimal action and the observations
available before a round.  Here it is represented as the KL divergence of
their joint law from the product of their marginals.
-/

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Mutual information between the observed length-`t` bandit history and the
optimal action under the terminal Bayesian adversarial-bandit law. -/
noncomputable def bayesianHistoryMutualInformation {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) (pi : BanditPolicy k)
    (t : ℕ) (ht : t ≤ n) : ℝ :=
  let mu := bayesianAdversarialMeasure Q pi n le_rfl
  let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    fun s : Fin t ↦ p.2 (Fin.castLE ht s)
  let optimal := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
    bayesianOptimalAction p.1
  (klDiv (Measure.map (fun p ↦ (history p, optimal p)) mu)
    ((Measure.map history mu).prod (Measure.map optimal mu))).toReal

end BanditAlgorithm


