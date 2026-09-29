-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_martingale
-- name    : MarkovMixing.evolving_sets_martingale
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:05.961835+00:00
-- url     : https://prove2.me/theorems/a56899bd-8e64-47eb-9d6b-6f6203bee1cb
-- title:
--   $\pi(S_t)$ is a martingale
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with strictly positive stationary distribution $\pi$, and write $Q(S,y)=\sum_{x\in S}\pi(x)P(x,y)$ for the stationary flow from a set $S$ into a state $y$. The **evolving-set process** is the Markov chain on subsets of $V$ that, from $S$, draws $u$ uniform on $(0,1]$ and passes to the superlevel set $\{y:Q(S,y)/\pi(y)\ge u\}$; its transition probability from $S$ to $T$ is the length of the interval of thresholds realizing $T$. A process adapted to a chain is a **martingale** when its one-step conditional expectation is neutral (the pointwise finite-sum identity of this mission's definitions).
--
--   The theorem (Lemma 17.13 of Levin–Peres–Wilmer) asserts that the stationary mass of the evolving set,
--   $$M_t\;=\;\pi(S_t)\;=\;\sum_{v\in S_t}\pi(v),$$
--   is a martingale for the evolving-set process: for every set $S$, $\;\sum_TK(S,T)\,\pi(T)=\pi(S)$, where $K$ is the process's transition matrix.
--
--   The mass gained when the threshold $u$ is small exactly balances the mass lost when it is large — stationarity of $\pi$ in disguise. This martingale is the engine of the whole chapter: the goal theorem controls the *square root* $\sqrt{\pi(S_t)}$ as a strict supermartingale whose decay rate is the bottleneck constant, and optional stopping converts that decay into mixing bounds.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 17.4, Lemma 17.13, p. 236

import Definitions.Def_mm_martingale

namespace MarkovMixing

/-- **Lemma 17.13** (LPW): for the evolving-set process, the sequence
`π(S_t)` is a martingale. -/
theorem evolving_sets_martingale {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (hpos : ∀ x : V, 0 < π x) :
    IsChainMartingale (evolvingSets P π)
      (fun t ω => ∑ v ∈ ω (Fin.last t), π v) := by
  sorry

end MarkovMixing
