-- Prove2me | Theorems.Thm_MarkovMixing_metropolized_stationary
-- name    : MarkovMixing.metropolized_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:14:50.204487+00:00
-- url     : https://prove2.me/theorems/4dae4f73-8cb9-49b0-9612-2f5ce37dfe2d
-- title:
--   Section 3.2.2 -- the Metropolis-Hastings chain for a general base chain
-- statement:
--   Let $\Psi$ be an arbitrary stochastic matrix on a finite state space $V$ (a base chain, not assumed symmetric), and let $\pi$ be a strictly positive probability distribution on $V$. The **Metropolis–Hastings chain** built from this pair proposes a move from $x$ to $y$ with probability $\Psi(x,y)$ and accepts it with probability
--   $$\min\!\Bigl(1,\;\frac{\pi(y)\,\Psi(y,x)}{\pi(x)\,\Psi(x,y)}\Bigr),$$
--   staying at $x$ on rejection; the acceptance ratio weighs the proposal probabilities of the two directions against the target masses.
--
--   The theorem asserts that this chain is a genuine Markov chain (nonnegative entries, rows summing to one), that it satisfies the **detailed balance** equations $\pi(x)\,M(x,y)=\pi(y)\,M(y,x)$ — reversibility with respect to $\pi$ — and that $\pi$ is a **stationary distribution** for it: $\sum_x\pi(x)\,M(x,y)=\pi(y)$ for every $y$. This is Exercise 3.1 of Levin–Peres–Wilmer, the general (non-symmetric) form of the Metropolis construction of §3.2.2.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 3.2.2, Eq. (3.5) and Exercise 3.1, p. 40

import Definitions.Def_mm_mcmc

namespace MarkovMixing

/-- **§3.2.2, Exercise 3.1** (LPW): the Metropolized chain built from a
general stochastic base chain `Ψ` and a positive target distribution `π` is a
Markov chain, reversible with respect to `π`, with stationary distribution
`π`. -/
theorem metropolized_stationary {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hΨ : IsStochastic Ψ)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x) :
    IsStochastic (metropolized Ψ π) ∧
    DetailedBalance (metropolized Ψ π) π ∧
    IsStationary (metropolized Ψ π) π := by
  sorry

end MarkovMixing
