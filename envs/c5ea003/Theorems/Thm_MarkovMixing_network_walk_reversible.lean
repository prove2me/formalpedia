-- Prove2me | Theorems.Thm_MarkovMixing_network_walk_reversible
-- name    : MarkovMixing.network_walk_reversible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:59:42.219609+00:00
-- url     : https://prove2.me/theorems/fc94cc7c-df80-4d87-8d13-bb2409ca3acd
-- title:
--   Section 9.1 -- the network walk is reversible
-- statement:
--   A **network** on a finite vertex set $V$ is a conductance function $c$: a symmetric assignment $c(x,y)=c(y,x)\ge0$ of nonnegative weights to pairs of vertices. Write $c(x)=\sum_yc(x,y)$ for the total conductance at the vertex $x$ — assumed strictly positive at every vertex — and $c_G=\sum_xc(x)$ for the total over all vertices. The **weighted random walk** on the network steps from $x$ to $y$ with probability proportional to the conductance:
--   $$P(x,y)=\frac{c(x,y)}{c(x)}.$$
--
--   The theorem (§9.1 of Levin–Peres–Wilmer) asserts:
--
--   1. $P$ is a genuine Markov chain: nonnegative entries with every row summing to one;
--   2. $P$ satisfies the **detailed balance** equations $\pi(x)P(x,y)=\pi(y)P(y,x)$ with respect to the distribution $\pi(x)=c(x)/c_G$ — it is reversible;
--   3. $\pi$ is a **stationary distribution** for $P$: $\sum_x\pi(x)P(x,y)=\pi(y)$ for every $y$.
--
--   This is the dictionary's first entry: every network yields a reversible chain, and conversely every reversible chain arises this way — which is why the electrical machinery of Chapters 9–10 computes hitting times of reversible chains.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 9.1, pp. 115-116

import Definitions.Def_mm_network

namespace MarkovMixing

/-- **§9.1** (LPW): the weighted random walk on a network is a Markov chain,
reversible with respect to `π(x) = c(x)/c_G`, which is therefore its
stationary distribution. -/
theorem network_walk_reversible {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (c : V → V → ℝ) (hc : IsConductance c)
    (hpos : ∀ x : V, 0 < vertexConductance c x) :
    IsStochastic (networkWalk c) ∧
    DetailedBalance (networkWalk c)
      (fun x => vertexConductance c x / totalConductance c) ∧
    IsStationary (networkWalk c)
      (fun x => vertexConductance c x / totalConductance c) := by
  sorry

end MarkovMixing
