-- Prove2me | Theorems.Thm_MarkovMixing_sep_tv_relation
-- name    : MarkovMixing.sep_tv_relation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:28:33.17315+00:00
-- url     : https://prove2.me/theorems/e39fbedc-a300-4205-ac10-9303ac09ca02
-- title:
--   Separation vs total variation: $s(2t)\le 1-(1-\bar d(t))^2$
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with stationary distribution $\pi$, reversible with respect to it (detailed balance: $\pi(x)P(x,y)=\pi(y)P(y,x)$). Two ways of measuring distance from stationarity at time $t$: the **maximal separation distance**
--   $$s(t)=\max_{x,y\in V}\Bigl(1-\frac{P^t(x,y)}{\pi(y)}\Bigr),$$
--   which is small only when every transition probability has caught up with its stationary value, and the **worst pairwise total variation distance** $\bar d(t)=\max_{x,y}\|P^t(x,\cdot)-P^t(y,\cdot)\|_{TV}$, with $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ (Mission II).
--
--   The theorem (Lemma 19.3, Aldous–Diaconis; Levin–Peres–Wilmer) asserts: for every time $t$,
--   $$s(2t)\;\le\;1-\bigl(1-\bar d(t)\bigr)^2.$$
--
--   Separation at twice the time is controlled by total variation at the original time: once the chain is well mixed in total variation, running it for the same time again brings every individual transition probability up to nearly its stationary value. The proof writes $P^{2t}(x,y)$ as a sum over midpoints, applies reversibility to fold the two halves, and uses Cauchy–Schwarz. In this mission the lemma is the bridge from cover-time estimates (which control $\bar d$ for the lamplighter chain) to the separation bounds in the lamplighter mixing theorem.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 19.2, Lemma 19.3 (Aldous--Diaconis), Eq. (19.8), p. 260

import Definitions.Def_mm_cutoff

namespace MarkovMixing

/-- **Lemma 19.3** (Aldous–Diaconis; LPW): for a reversible chain, the
separation and total variation distances satisfy
`s(2t) ≤ 1 − (1 − d̄(t))²`. -/
theorem sep_tv_relation {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (t : ℕ) :
    sepSup P π (2 * t) ≤ 1 - (1 - distPairs P t) ^ 2 := by
  sorry

end MarkovMixing
