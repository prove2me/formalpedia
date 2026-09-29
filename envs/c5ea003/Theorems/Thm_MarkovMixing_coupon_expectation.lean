-- Prove2me | Theorems.Thm_MarkovMixing_coupon_expectation
-- name    : MarkovMixing.coupon_expectation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:43:42.753201+00:00
-- url     : https://prove2.me/theorems/10d96d2e-3a05-42b6-a887-614d239dfb6f
-- title:
--   Proposition 2.3 -- the coupon collector's expected time
-- statement:
--   The expected number of independent uniform draws needed to collect all $n$ coupon types is $$\mathbb{E}(\tau)=n\sum_{k=1}^n\frac{1}{k},$$ where $\mathbb{E}(\tau)$ is encoded by the tail-sum $\sum_{t\ge0}\mathbb{P}\{\tau>t\}$ and $\mathbb{P}\{\tau>t\}$ is the fraction of draw sequences of length $t$ that miss some type.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.2, Proposition 2.3, p. 22

import Definitions.Def_mm_classical

namespace MarkovMixing

/-- **Proposition 2.3** (LPW): the expected number of uniform draws needed to
collect all `n` coupon types is `n ∑_{k=1}^n 1/k`. -/
theorem coupon_expectation (n : ℕ) (hn : 1 ≤ n) :
    couponExpTime n = n * ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k := by
  sorry

end MarkovMixing
