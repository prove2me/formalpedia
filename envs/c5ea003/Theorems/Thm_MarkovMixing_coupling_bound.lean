-- Prove2me | Theorems.Thm_MarkovMixing_coupling_bound
-- name    : MarkovMixing.coupling_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:09:18.972683+00:00
-- url     : https://prove2.me/theorems/7461cbd8-3973-4007-a705-243aced16acb
-- title:
--   Theorem 5.2 and Corollary 5.3 -- the coupling bound
-- statement:
--   Let $P$ be a Markov chain on a finite state space $V$ with stationary distribution $\pi$, and write $P^t(x,\cdot)$ for the distribution at time $t$ started at $x$, $\|\mu-\nu\|_{TV}=\max_{A\subseteq V}|\mu(A)-\nu(A)|$ for the total variation distance, and $d(t)=\max_x\|P^t(x,\cdot)-\pi\|_{TV}$ for the worst-case distance to stationarity. A **Markovian coupling** of $P$ is a Markov chain on ordered pairs of states each of whose two coordinates, viewed on its own, moves according to $P$, and which keeps the two coordinates together once they coincide. For such a coupling started at the pair $(x,y)$, the **coupling time** $\tau_{\mathrm{couple}}$ is the first time the pair chain reaches the diagonal $\{(v,v)\}$ — the moment the two copies meet.
--
--   Suppose a Markovian coupling $Q_{x,y}$ of $P$ is given for every pair of starting states. The theorem (Theorem 5.2 and Corollary 5.3 of Levin–Peres–Wilmer) asserts:
--
--   1. for every pair $x,y$ and time $t$, the rows of $P^t$ are close whenever the coupling has probably met: $\bigl\|P^t(x,\cdot)-P^t(y,\cdot)\bigr\|_{TV}\le\mathbb P_{x,y}\{\tau_{\mathrm{couple}}>t\}$;
--   2. consequently $d(t)\le\max_{x,y}\mathbb P_{x,y}\{\tau_{\mathrm{couple}}>t\}$.
--
--   This is the engine of the coupling method: to bound mixing, build a coupling that meets fast.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 5.2, Theorem 5.2 and Corollary 5.3, pp. 64-65

import Definitions.Def_mm_coupling

namespace MarkovMixing

/-- **Theorem 5.2 and Corollary 5.3** (LPW): if each pair of starting states
carries a Markovian coupling of the chain (staying together after meeting),
then `‖P^t(x,·) − P^t(y,·)‖_TV ≤ P_{x,y}{τ_couple > t}`, and hence
`d(t) ≤ max_{x,y} P_{x,y}{τ_couple > t}`, where `τ_couple` is the hitting
time of the diagonal for the pair chain. -/
theorem coupling_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π)
    (Q : V → V → Matrix (V × V) (V × V) ℝ)
    (hQ : ∀ x y : V, IsMarkovianCoupling P (Q x y)) (t : ℕ) :
    (∀ x y : V, tvDist (rowDist P t x) (rowDist P t y) ≤
      setAvoidTailProb (Q x y) (x, y) (pairDiagonal V) t) ∧
    distStationary P π t ≤
      ⨆ p : V × V, setAvoidTailProb (Q p.1 p.2) p (pairDiagonal V) t := by
  sorry

end MarkovMixing
