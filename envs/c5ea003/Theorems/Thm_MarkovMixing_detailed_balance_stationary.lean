-- Prove2me | Theorems.Thm_MarkovMixing_detailed_balance_stationary
-- name    : MarkovMixing.detailed_balance_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:42:38.7082+00:00
-- url     : https://prove2.me/theorems/71a4fc11-0f9d-418d-a4da-91c6ffdc40fd
-- title:
--   Proposition 1.19 -- detailed balance implies stationarity
-- statement:
--   If a probability distribution $\pi$ satisfies the detailed balance equations $\pi(x)P(x,y)=\pi(y)P(y,x)$ for all states $x,y$ of a stochastic matrix $P$, then $\pi$ is stationary for $P$. This is the standard tool for identifying stationary distributions of reversible chains.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.6, Proposition 1.19, p. 14

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Proposition 1.19** (LPW): any probability distribution satisfying the
detailed balance equations is stationary. -/
theorem detailed_balance_stationary {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (π : V → ℝ) (hπ : IsDist π)
    (hdb : DetailedBalance P π) :
    IsStationary P π := by
  sorry

end MarkovMixing
