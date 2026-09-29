-- Prove2me | Theorems.Thm_BanditAlgorithm_klucb_feasibility_optimal_underestimation_count_bound
-- name    : BanditAlgorithm.klucb_feasibility_optimal_underestimation_count_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T06:01:25.676079+00:00
-- url     : https://prove2.me/theorems/d3ba2b23-aaff-45f3-aebc-080e1d80ddd7
-- title:
--   KL-UCB optimal-arm underestimation count bound
-- statement:
--   This is the optimal-arm underestimation count bound used in the finite-time analysis of KL-UCB.
--
--   Consider a Bernoulli bandit with means in $[0,1]$, a KL-UCB policy $\pi$, an optimal arm $a$, a suboptimal arm $i$, and $0<\varepsilon<\Delta_i$.  Along a length-$n$ history, count the rounds on which arm $i$ is selected and the candidate value $\mu^*-\varepsilon$ is infeasible for arm $a$'s KL-UCB confidence set.  Equivalently, after initialization this is the event
--
--   $$
--   \overline d\!\left(\widehat\mu_a(t-1),\,\mu^*-\varepsilon\right)
--   >
--   \frac{\log f(t)}{T_a(t-1)},
--   \qquad
--   f(t)=1+t\log^2 t,
--   $$
--
--   where $\overline d(p,q)=d(p,q)\mathbf 1_{\{p\le q\}}$.  The expected number of such selected rounds satisfies
--
--   $$
--   \mathbb E_{\nu,\pi}\!\left[N^{\mathrm{under}}_{a,i,\varepsilon}(n)\right]
--   \le \frac{2}{\varepsilon^2}.
--   $$
--
--   This is the bandit-history formulation of Lemma 10.7 and supplies the optimal-arm failure term in the proof of the finite-time KL-UCB regret bound.
--
--   **Formalization Note** `klucbFeasibilityFailureCount` stores the optimal-arm underestimation count in its first component.  The predicate `IsKLUCBPolicy` is included because the policy's initialization rule is needed to charge at most one selected round before arm $a$ has an empirical mean.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Lemma 10.7 and proof, printed p. 138; using Lemma 10.2(c), printed p. 134, and Corollary 10.4 Eq. (10.3), printed p. 135.

import Definitions.Def_klucbFeasibilityFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.klucb_feasibility_optimal_underestimation_count_bound
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
        (fun h ↦
          (BanditAlgorithm.klucbFeasibilityFailureCount ν a i ε h).1) ≤
      2 / ε ^ 2 := by
  sorry
