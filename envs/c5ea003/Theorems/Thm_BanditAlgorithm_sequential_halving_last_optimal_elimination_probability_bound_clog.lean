-- Prove2me | Theorems.Thm_BanditAlgorithm_sequential_halving_last_optimal_elimination_probability_bound_clog
-- name    : BanditAlgorithm.sequential_halving_last_optimal_elimination_probability_bound_clog
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T16:38:20.746603+00:00
-- url     : https://prove2.me/theorems/aa9cf3ab-1ec5-47fb-938c-696d850c51e0
-- title:
--   One-phase elimination of the last optimal arm
-- statement:
--   Let $L=\lceil\log_2 k\rceil$ and fix $\ell<L$. Under the same sorted $1$-subgaussian, budget, and $H_2$ assumptions, the probability that phase $\ell$ eliminates the last optimal arm from a complete Sequential Halving active-set chain is bounded by
--
--   $$
--   \mathbb P(A_\ell\text{ contains an optimal arm and }A_{\ell+1}\text{ contains none})
--   \le 3\exp\!\left(-\frac{n}{16H_2L}\right).
--   $$
--
--   This is the one-phase estimate in the Sequential Halving analysis. Its union over the $L$ phases yields the full bad-final probability bound.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Exercise 33.8(b)–(e), printed pp. 419–420.

import Definitions.Def_SequentialHalvingBadFinal

open MeasureTheory

theorem BanditAlgorithm.sequential_halving_last_optimal_elimination_probability_bound_clog
    {k n : ℕ} (ν : StochasticBandit k) (hν : IsSubgaussianBandit 1 ν)
    (hsorted : ∀ i j : Fin k, i ≤ j → banditArmMean ν j ≤ banditArmMean ν i)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < banditGap ν i →
      ((i : ℕ) + 1 : ℝ) / banditGap ν i ^ 2 ≤ H₂)
    (π : BanditPolicy k) (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) :
    (banditMeasure ν π n).real
        {h | IsSeqHalvingLastOptimalEliminationAt k n ν h ℓ} ≤
      3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  sorry
