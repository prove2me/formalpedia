-- Prove2me | Theorems.Thm_BanditAlgorithm_gittins_prevailing_charge_regular
-- name    : BanditAlgorithm.gittins_prevailing_charge_regular
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T16:27:10.462058+00:00
-- url     : https://prove2.me/theorems/ec51601d-1c2b-4845-9903-4806e55b13fa
-- title:
--   Measurability and integrability of prevailing charges
-- statement:
--   For a measurable reward and discount factor $0<\alpha<1$, assume discounted absolute rewards are integrable.  Then the Gittins-index function is measurable.  Consequently, at every finite horizon each arm's current prevailing charge is a measurable function of the observed history, and the prevailing charge selected in the next bandit step is integrable under the joint history/action/transition law.
--
--   This regularity package is the measure-theoretic interface needed by the common reward-stack coupling and by finite prevailing-charge expectations.
--
--   **Formalization Note** The last assertion is uniform over the horizon, policy, and initial state vector; the selected arm is the action coordinate in the one-step product kernel.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (free online edition), https://tor-lattimore.com/downloads/book/book.pdf, Assumption 35.6 and §35.4 proof of Theorem 35.9, Parts 1–2, printed pp. 447 and 451–453 / PDF pp. 455 and 459–461.

import Definitions.Def_GittinsTerminalPotential

open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.gittins_prevailing_charge_regular
    {k : ℕ} {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P]
    {r : S → ℝ} (hr : Measurable r)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hint : DiscountedRewardIntegrable P r α) :
    Measurable (gittinsIndex P r α) ∧
      (∀ (n : ℕ) (i : Fin k),
        Measurable (fun h : MarkovBanditHistory k S n ↦
          currentHistoryPrevailingCharge
            (gittinsIndex P r α) n h i)) ∧
      (∀ (n : ℕ) (π : MarkovBanditPolicy k S) (x : Fin k → S),
        Integrable
          (fun p : MarkovBanditHistory k S n × (Fin k × S) ↦
            currentHistoryPrevailingCharge
              (gittinsIndex P r α) n p.1 p.2.1)
          ((markovBanditMeasure P π x n).compProd
            (markovBanditStepKernel P π n))) := by
  sorry
