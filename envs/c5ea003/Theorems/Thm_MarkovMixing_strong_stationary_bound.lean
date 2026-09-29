-- Prove2me | Theorems.Thm_MarkovMixing_strong_stationary_bound
-- name    : MarkovMixing.strong_stationary_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:10:59.631057+00:00
-- url     : https://prove2.me/theorems/3511285e-0716-41f8-9229-aad9273a1431
-- title:
--   Proposition 6.10 -- the strong stationary time bound
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with stationary distribution $\pi$. Write $P^t(x,\cdot)$ for the distribution at time $t$ started at $x$, $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance, and $d(t)=\max_x\|P^t(x,\cdot)-\pi\|_{TV}$ for the worst-case distance to stationarity. A **strong stationary time** $\tau$ for the chain started at $x$ is a randomized stopping rule that stops in finite time almost surely, with the stopped state distributed exactly as $\pi$ and independent of the stopping time.
--
--   The theorem (Proposition 6.10 of Levin–Peres–Wilmer) asserts: if a single stopping rule is a strong stationary time from **every** starting state, then for every time $t$
--   $$d(t)\;\le\;\max_{x\in V}\,\mathbb P_x\{\tau>t\}.$$
--   To bound the mixing time of a chain it therefore suffices to construct one strong stationary time and control its tail uniformly in the start.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 6.4, Proposition 6.10, p. 79

import Definitions.Def_mm_stopping

namespace MarkovMixing

/-- **Proposition 6.10** (LPW): if `τ` is a strong stationary time from every
starting state, then `d(t) ≤ max_x P_x{τ > t}`. -/
theorem strong_stationary_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (s : ∀ t : ℕ, (Fin (t + 1) → V) → ℝ)
    (hs : ∀ x : V, IsStrongStationaryTime P π x s) (t : ℕ) :
    distStationary P π t ≤ ⨆ x : V, stopTailProb P x s t := by
  sorry

end MarkovMixing
