-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_feasibility_pull_count_split
-- name    : BanditAlgorithm.bandit_kl_ucb_feasibility_pull_count_split
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T04:22:22.383121+00:00
-- url     : https://prove2.me/theorems/4a93f4c2-b32d-4d4f-91f0-7cf84ab330e2
-- title:
--   KL-UCB pathwise feasibility-count split
-- statement:
--   Consider KL-UCB on a Bernoulli bandit with arm means $\mu_j\in[0,1]$. Fix an optimal arm $a$, a suboptimal arm $i$, and a tolerance $0<\varepsilon<\Delta_i$, where $\Delta_i=\mu^\star-\mu_i$. Let $U_i(n)$ be the number of times arm $i$ is selected before horizon $n$. Let $L_{a,i,\varepsilon}(n)$ count selections of $i$ caused by incomplete initialization or failure of the optimal arm's KL threshold test, and let $V_{i,\varepsilon}(n)$ count initialized selections of $i$ for which the selected arm passes its KL threshold test.
--
--   Then the expected pull count is bounded by the expectations of these two failure counts:
--
--   $$
--   \mathbb E[U_i(n)]
--   \le
--   \mathbb E[L_{a,i,\varepsilon}(n)]
--   +
--   \mathbb E[V_{i,\varepsilon}(n)].
--   $$
--
--   Indeed, on every realized Bernoulli reward history, if KL-UCB selects $i$, maximality of its index implies a dichotomy. Either the optimal arm does not regard $\mu^\star-\varepsilon$ as feasible, or the selected arm does. Thus every selection of $i$ is charged pathwise to exactly one of the two displayed counts, and integration gives the result.
--
--   This lemma is the deterministic-probabilistic interface in the proof of the finite-time KL-UCB regret bound: subsequent concentration lemmas bound the two expectations separately.
--
--   Formalization Note: The policy hypothesis is expressed by `IsKLUCBPolicy`; the Bernoulli-bandit equality supplies the almost-sure $\{0,1\}$-valued reward support needed to place empirical means in $[0,1]$. The Lean proof first establishes the inequality on every supported finite history, then verifies measurability and integrability of all three finite counts before applying monotonicity of the integral.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Algorithm 8 and proof of Theorem 10.6, printed pp. 137 and 139–140 (PDF pp. 126 and 128–129).

import Definitions.Def_klucbFeasibilityFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_kl_ucb_feasibility_pull_count_split
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : BanditAlgorithm.StochasticBandit k)
    (hν : ν = BanditAlgorithm.bernoulliBandit μvec hμ)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsKLUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hε : 0 < ε) (hεgap : ε < BanditAlgorithm.banditGap ν i) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).2) := by
  sorry
