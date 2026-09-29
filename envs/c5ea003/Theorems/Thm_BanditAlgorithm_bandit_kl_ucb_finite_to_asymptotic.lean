-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_finite_to_asymptotic
-- name    : BanditAlgorithm.bandit_kl_ucb_finite_to_asymptotic
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:34:20.222475+00:00
-- url     : https://prove2.me/theorems/a04e5f0c-a9b7-4488-a643-d5f29bdf0a84
-- title:
--   From the finite KL-UCB bound to the asymptotic constant
-- statement:
--   This is the limiting argument that turns the finite-horizon KL-UCB estimate into its asymptotic regret guarantee.
--
--   Consider a finite Bernoulli bandit with means $\mu_i\in[0,1]$, optimal mean $\mu^\star$, gaps $\Delta_i=\mu^\star-\mu_i$, and a KL-UCB policy. Assume that for every horizon $n$ and every positive arm-dependent pair $\varepsilon_{1,i},\varepsilon_{2,i}$ with $\varepsilon_{1,i}+\varepsilon_{2,i}<\Delta_i$, the standard finite-time bound of Theorem 10.6 holds. Then
--
--   $$
--   \limsup_{n\to\infty}\frac{R_n(\pi,\nu)}{\log n}
--   \le
--   \sum_{i:\Delta_i>0}\frac{\Delta_i}{d(\mu_i,\mu^\star)}.
--   $$
--
--   This theorem isolates the analytic passage from the non-asymptotic KL-UCB estimate to its optimal logarithmic leading constant.
--
--   **Formalization Note** The entire finite-horizon estimate is supplied as a hypothesis. The conclusion uses the extended-nonnegative-real limsup representation from the mission theorem.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, asymptotic claim of Theorem 10.6, printed p. 137; Exercise 10.2 and its hint, printed pp. 141–142: choose ε₁ and ε₂ to decrease slowly with n and use the first claim.

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_kl_ucb_finite_to_asymptotic
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π)
    (hfinite :
      ∀ n : ℕ, ∀ ε₁ ε₂ : Fin k → ℝ,
        (∀ i, 0 < banditGap ν i →
          0 < ε₁ i ∧ 0 < ε₂ i ∧
            ε₁ i + ε₂ i < banditGap ν i) →
        banditRegret ν π n ≤
          ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
            banditGap ν i *
              (Real.log (klucbExploration n) /
                  bernoulliRelativeEntropy
                    (banditArmMean ν i + ε₁ i)
                    (banditOptimalMean ν - ε₂ i) +
                1 / (2 * ε₁ i ^ 2) + 2 / ε₂ i ^ 2)) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal (banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        ENNReal.ofReal (banditGap ν i) /
          ENNReal.ofReal
            (bernoulliRelativeEntropy (banditArmMean ν i)
              (banditOptimalMean ν)) := by
  sorry
