-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_bernoulli_kl_lower_tail
-- name    : BanditAlgorithm.bandit_adaptive_stopped_bernoulli_kl_lower_tail
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T05:53:36.307169+00:00
-- url     : https://prove2.me/theorems/f08a8bb5-b8f7-4a08-8d82-aefe335d0be0
-- title:
--   Adaptive stopped Bernoulli KL lower-tail bound
-- statement:
--   This is the adaptive-policy version of the lower-tail Bernoulli KL–Chernoff bound.
--
--   Fix a Bernoulli bandit with arm means $\mu_j\in[0,1]$, an arbitrary adaptive policy $\pi$, an arm $i$ with $0<\mu_i<1$, and an integer $u\ge1$. On a length-$n$ bandit history, let $T_i(n)$ be the number of pulls of arm $i$, and, whenever $T_i(n)\ge u$, let $\widehat\mu_{i,u}$ be the average of the first $u$ rewards obtained from arm $i$. Then for every real $c$,
--
--   $$
--   \mathbb P_{\nu,\pi}^{\,n}\!\left(
--     T_i(n)\ge u,\quad
--     \widehat\mu_{i,u}\in[0,1],\quad
--     \widehat\mu_{i,u}<\mu_i,\quad
--     d(\widehat\mu_{i,u},\mu_i)>c
--   \right)
--   \le \exp(-uc),
--   $$
--
--   where $d(p,q)$ is the binary relative entropy.
--
--   This source-faithful adaptive form makes Corollary 10.4, Eq. (10.3), reusable at data-dependent arm-pull times in KL-UCB analyses; it is the concentration input required by Lemma 10.7.
--
--   **Formalization Note** The stopped average is represented by `armStoppedCenteredSum` plus $u\mu_i$, divided by $u$. The interval condition is stated explicitly because the stopped-sum interface is defined on every history. No independence assumption is imposed on the sequence of chosen actions: adaptivity is handled by the bandit measure.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Corollary 10.4 Eq. (10.3), printed p. 135; adaptive reward-stack construction in §4.6, printed pp. 65–66.

import Definitions.Def_ucbStoppedCenteredSum
import Definitions.Def_bernoulliRelativeEntropy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_adaptive_stopped_bernoulli_kl_lower_tail
    {k n : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ j, μvec j ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    {π : BanditAlgorithm.BanditPolicy k} (i : Fin k)
    (u : ℕ) (hu : 0 < u)
    (hμ0 : 0 < μvec i) (hμ1 : μvec i < 1) (c : ℝ) :
    let stoppedAverage := fun h : BanditAlgorithm.BanditHistory k n ↦
      (BanditAlgorithm.armStoppedCenteredSum ν i u n h +
        μvec i * (u : ℝ)) / (u : ℝ)
    (BanditAlgorithm.banditMeasure ν π n).real
        {h |
          u ≤ BanditAlgorithm.armPullCount i h ∧
          stoppedAverage h ∈ Set.Icc (0 : ℝ) 1 ∧
          stoppedAverage h < μvec i ∧
          c < BanditAlgorithm.bernoulliRelativeEntropy
            (stoppedAverage h) (μvec i)} ≤
      Real.exp (-((u : ℝ) * c)) := by
  sorry
