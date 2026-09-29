-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_pull_count_failure_split
-- name    : BanditAlgorithm.bandit_kl_ucb_pull_count_failure_split
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:26:42.345611+00:00
-- url     : https://prove2.me/theorems/c3850e56-3c19-42d3-9963-589102e24bda
-- title:
--   KL-UCB pull-count failure split
-- statement:
--   This is the selected-round decomposition used in the finite-time proof of KL-UCB.
--
--   Fix an optimal arm $a$, an arm $i$, a horizon $n$, and a tolerance $\varepsilon$. Let $L_{a,i,\varepsilon}(n)$ count selections of $i$ made during initialization or while the optimal-arm index is at most $\mu^\star-\varepsilon$, and let $H_{a,i,\varepsilon}(n)$ count initialized selections of $i$ whose own index is at least $\mu^\star-\varepsilon$. If the policy follows the KL-UCB selection rule, then
--
--   $$
--   \mathbb E_{\nu,\pi}[T_i(n)]
--   \le
--   \mathbb E_{\nu,\pi}[L_{a,i,\varepsilon}(n)]
--   +
--   \mathbb E_{\nu,\pi}[H_{a,i,\varepsilon}(n)].
--   $$
--
--   This deterministic-policy bridge separates the pull count into the two probabilistic failure modes controlled by Lemmas 10.7 and 10.8.
--
--   **Formalization Note** The expectations are integrals against the canonical finite-history bandit measure. The statement records that $a$ has optimal mean, matching its role in the source argument.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, proof of Theorem 10.6, displayed pull-count decomposition on printed p. 139.

import Definitions.Def_klucbFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_kl_ucb_pull_count_failure_split {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsKLUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFailureCount ν a i ε h).2) := by
  sorry
