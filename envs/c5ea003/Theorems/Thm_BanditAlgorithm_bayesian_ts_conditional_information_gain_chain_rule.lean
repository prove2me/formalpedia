-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_information_gain_chain_rule
-- name    : BanditAlgorithm.bayesian_ts_conditional_information_gain_chain_rule
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T01:48:49.63297+00:00
-- url     : https://prove2.me/theorems/6d6f8909-688b-4b89-82b0-e5252ba4eeb1
-- title:
--   Conditional mutual-information chain rule for one bandit round
-- statement:
--   Fix a round $t$ and let $g_t(h)$ denote the conditional mutual information between the optimal arm and the new arm--reward observation, given the pre-round history. Then
--
--   $$
--   \int g_t(h)\,\nu_t(dh)\le I(A^*;H_{t+1})-I(A^*;H_t).
--   $$
--
--   This is the conditional mutual-information chain rule used to account for the information acquired in one bandit round.
--
--   **Formalization Note** Mutual information is represented by Kullback--Leibler divergence from the product of marginals, and histories are terminal-law prefix maps.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; conditional-law and Bayes/chain-rule formalization.

import Definitions.Def_BayesianTSRoundConditionalGains
import Mathlib.InformationTheory.KullbackLeibler.ChainRule

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- Conditional mutual-information accounting for one additional bandit
observation. -/
theorem bayesian_ts_conditional_information_gain_chain_rule
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    {pi : BanditPolicy k} (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    (∫ h, bayesianTSRoundConditionalInformationGain Q pi t h ∂nu) ≤
      bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
        bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2) := by
  sorry

end BanditAlgorithm
