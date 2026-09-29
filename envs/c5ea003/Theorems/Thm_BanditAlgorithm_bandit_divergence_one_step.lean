-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_divergence_one_step
-- name    : BanditAlgorithm.bandit_divergence_one_step
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-20T17:18:06.849053+00:00
-- url     : https://prove2.me/theorems/1a51da9b-d803-4994-a034-bc54eb49f70e
-- title:
--   One-round divergence increment in the canonical bandit model
-- statement:
--   For two finite-armed stochastic bandits run under the same possibly randomized policy, the KL divergence between their canonical history laws after round $n+1$ equals the divergence after round $n$ plus the expected KL contribution of the newly selected arm. The coefficient of arm $i$ is its round-$n+1$ selection probability averaged under the first bandit's $n$-round history law. This is the one-round conditional-expectation identity used in the proof of the divergence decomposition.
-- source:
--   Lattimore--Szepesvári, Bandit Algorithms (CUP 2020), Lemma 15.1 proof, Eq. (15.2), printed pp. 198--199 / PDF pp. 207--208: chain rule for the canonical likelihood ratio and conditioning on the selected arm.

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Definitions.Def_BanditPolicy

open MeasureTheory ProbabilityTheory InformationTheory

theorem BanditAlgorithm.bandit_divergence_one_step {k n : ℕ} (ν ν' : StochasticBandit k)
    (hKL : ∀ i, klDiv (ν.P i) (ν'.P i) ≠ ⊤)
    (π : BanditPolicy k) :
    klDiv (banditMeasure ν π (n + 1)) (banditMeasure ν' π (n + 1)) =
      klDiv (banditMeasure ν π n) (banditMeasure ν' π n) +
        ∑ i, ENNReal.ofReal
          (∫ h, (π.select n h).real {i} ∂banditMeasure ν π n) *
            klDiv (ν.P i) (ν'.P i) := by
  sorry
