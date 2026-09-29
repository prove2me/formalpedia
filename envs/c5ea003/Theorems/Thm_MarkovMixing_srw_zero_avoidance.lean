-- Prove2me | Theorems.Thm_MarkovMixing_srw_zero_avoidance
-- name    : MarkovMixing.srw_zero_avoidance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:44:15.607511+00:00
-- url     : https://prove2.me/theorems/d0067493-f4ed-4825-a17a-7aa0bf9acd7f
-- title:
--   Theorem 2.17 -- avoiding zero for $r$ steps
-- statement:
--   For simple random walk on $\mathbb{Z}$ started at $k>0$, the probability of not visiting $0$ within $r$ steps is at most $$\mathbb{P}_k\{\tau_0>r\}\le\frac{12k}{\sqrt r}.$$ The probability is the exact fraction of the $2^r$ sign strings whose walk avoids $0$ at all times $t\le r$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.7, Theorem 2.17, p. 30

import Definitions.Def_mm_classical

namespace MarkovMixing

/-- **Theorem 2.17** (LPW): for simple random walk on `ℤ` started at `k > 0`,
the probability of not visiting `0` within `r` steps is at most `12k/√r`. -/
theorem srw_zero_avoidance (r : ℕ) (hr : 0 < r) (k : ℤ) (hk : 0 < k) :
    ((Finset.univ.filter fun ω : Fin r → Bool =>
        ∀ t ≤ r, srwPos k ω t ≠ 0).card : ℝ) / 2 ^ r ≤
      12 * (k : ℝ) / Real.sqrt r := by
  sorry

end MarkovMixing
