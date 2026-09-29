-- Prove2me | Theorems.Thm_MarkovMixing_dist_le_distPairs
-- name    : MarkovMixing.dist_le_distPairs
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:16:05.913774+00:00
-- url     : https://prove2.me/theorems/f42f7f39-477c-477a-bc39-1049b65d1f94
-- title:
--   Lemma 4.11 -- comparing $d(t)$ and $\bar d(t)$
-- statement:
--   Let $P$ be the transition matrix of a Markov chain on a finite state space $V$ with stationary distribution $\pi$ (that is, $\sum_x\pi(x)P(x,y)=\pi(y)$ for all $y$), and write $P^t(x,\cdot)$ for the distribution of the chain at time $t$ started at $x$, and $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance. Chapter 4 of Levin–Peres–Wilmer measures convergence by two quantities: the **worst-case distance to stationarity** and the **worst pairwise distance**,
--   $$d(t)=\max_{x\in V}\bigl\|P^t(x,\cdot)-\pi\bigr\|_{TV},\qquad \bar d(t)=\max_{x,y\in V}\bigl\|P^t(x,\cdot)-P^t(y,\cdot)\bigr\|_{TV}.$$
--
--   The theorem (Lemma 4.11) asserts that for every time $t$ these are equivalent up to a factor of two:
--   $$d(t)\;\le\;\bar d(t)\;\le\;2\,d(t).$$
--   The left inequality holds because $\pi$ is an average of the rows $P^t(y,\cdot)$; the right is the triangle inequality through $\pi$. The point of $\bar d$ is that, unlike $d$, it is submultiplicative — the subject of the companion lemma.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 4.4, Lemma 4.11, p. 53

import Definitions.Def_mm_mixing

namespace MarkovMixing

/-- **Lemma 4.11** (LPW): `d(t) ≤ d̄(t) ≤ 2 d(t)`. -/
theorem dist_le_distPairs {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (t : ℕ) :
    distStationary P π t ≤ distPairs P t ∧
    distPairs P t ≤ 2 * distStationary P π t := by
  sorry

end MarkovMixing
