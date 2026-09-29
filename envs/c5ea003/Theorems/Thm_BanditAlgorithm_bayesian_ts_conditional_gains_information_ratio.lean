-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_conditional_gains_information_ratio
-- name    : BanditAlgorithm.bayesian_ts_conditional_gains_information_ratio
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T01:39:20.598226+00:00
-- url     : https://prove2.me/theorems/5cbc56f3-cac3-40e3-8423-cf6d65cafca9
-- title:
--   Conditional Thompson information-ratio inequality
-- statement:
--   Fix a round $t$ of Bayesian Thompson sampling, and let $\nu_t$ denote the law of the history before that round. Let $r_t(h)$ be conditional expected regret and let $g_t(h)$ be the conditional mutual information between the optimal arm and the new arm--reward observation. Then $r_t$, $r_t^2$, and $g_t$ are integrable and, for $\nu_t$-almost every history,
--
--   $$
--   r_t(h)^2\le \frac{k}{2}g_t(h).
--   $$
--
--   This is the conditional information-ratio inequality at the core of Lemma 36.7 and is reusable independently of the later time-summation argument.
--
--   **Formalization Note** The reward-matrix prior is supported on $[0,1]^{n\times k}$, and Thompson sampling is expressed by equality of the posterior optimal-arm law with the policy kernel.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 36.7, printed p. 470 (free PDF p. 479), https://tor-lattimore.com/downloads/book/book.pdf; conditional-law and Bayes/chain-rule formalization.

import Definitions.Def_BayesianTSRoundConditionalGains
import Theorems.Thm_BanditAlgorithm_thompson_sampling_one_step_information_ratio_varying_reference

open MeasureTheory ProbabilityTheory InformationTheory

namespace BanditAlgorithm

/-- The conditional Thompson-sampling information-ratio inequality of
Lattimore--Szepesvari, Lemma 36.7. -/
theorem bayesian_ts_conditional_gains_information_ratio
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    let history := fun p : (Fin n → Fin k → ℝ) × BanditHistory k n ↦
      fun s : Fin t.1 ↦ p.2 (Fin.castLE (Nat.le_of_lt t.2) s)
    let nu := Measure.map history (bayesianAdversarialMeasure Q pi n le_rfl)
    Integrable (bayesianTSRoundConditionalRegretGain Q pi t) nu ∧
      Integrable (fun h ↦ bayesianTSRoundConditionalRegretGain Q pi t h ^ 2) nu ∧
      Integrable (bayesianTSRoundConditionalInformationGain Q pi t) nu ∧
      (∀ᵐ h ∂nu,
        bayesianTSRoundConditionalRegretGain Q pi t h ^ 2 ≤
          ((k : ℝ) / 2) * bayesianTSRoundConditionalInformationGain Q pi t h) := by
  sorry

end BanditAlgorithm
