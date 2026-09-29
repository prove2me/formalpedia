-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_high_probability_lower_bound_at_gap
-- name    : BanditAlgorithm.bandit_high_probability_lower_bound_at_gap
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-21T02:40:32.162922+00:00
-- url     : https://prove2.me/theorems/93adfc89-7beb-45fe-8ae0-1d1ac44291d4
-- title:
--   Theorem 17.1 fixed-gap testing core
-- statement:
--   This is the fixed-gap testing form used in the proof of Theorem 17.1. Let $k \ge 2$, $n \ge 1$, $B>0$, and let $\pi$ be a policy whose expected regret on every unit-variance Gaussian bandit with mean vector in $[0,1]^k$ is at most $B\sqrt{(k-1)n}$. Fix $\delta \in (0,1)$ and a gap $\Delta \in (0,1/2]$. If
--
--   $$2\delta \le \frac12 \exp\!\left(-2B\Delta\sqrt{\frac{n}{k-1}}\right),$$
--
--   then there is a mean vector $\mu \in [0,1]^k$ for which the random pseudo-regret $\bar R_n=\sum_i T_i(n)\Delta_i$ satisfies
--
--   $$\mathbb P_{\nu_\mu,\pi}\!\left(\bar R_n \ge \frac{\Delta n}{2}\right) \ge \delta.$$
--
--   This isolates the reusable Bretagnolle–Huber testing step before the final theorem tunes $\Delta$ as a function of $B,n,k,$ and $\delta$.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 17.1, printed pp. 216–217 / PDF pp. 225–226; Eq. (17.5) and the Bretagnolle–Huber/divergence display immediately before the tuned choice of Δ.

import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_high_probability_lower_bound_at_gap {k n : ℕ}
    (hk : 2 ≤ k) (hn : 1 ≤ n) {B : ℝ} (hB : 0 < B) (π : BanditPolicy k)
    (hbound : ∀ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      banditRegret (gaussianBandit μvec) π n ≤ B * Real.sqrt (((k : ℝ) - 1) * n))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (Δ : ℝ)
    (hΔpos : 0 < Δ) (hΔle : Δ ≤ 1 / 2)
    (htest : 2 * δ ≤ (1 / 2 : ℝ) *
      Real.exp (-2 * B * Δ * Real.sqrt ((n : ℝ) / ((k : ℝ) - 1)))) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      δ ≤ (banditMeasure (gaussianBandit μvec) π n).real
        {h | Δ * n / 2 ≤
          ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} := by sorry
