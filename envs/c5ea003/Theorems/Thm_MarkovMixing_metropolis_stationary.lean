-- Prove2me | Theorems.Thm_MarkovMixing_metropolis_stationary
-- name    : MarkovMixing.metropolis_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T15:14:35.864934+00:00
-- url     : https://prove2.me/theorems/1c7acbff-8192-485e-aa95-df9247eccf2f
-- title:
--   Section 3.2.1 -- the Metropolis chain for a symmetric base chain
-- statement:
--   Let $\Psi$ be a symmetric stochastic matrix on a finite state space $V$ (a proposal chain with $\Psi(x,y)=\Psi(y,x)$), and let $\pi$ be a strictly positive probability distribution on $V$. The **Metropolis chain** for this pair moves as follows: from the current state $x$ it proposes a state $y$ with probability $\Psi(x,y)$, accepts the proposal with probability $\min\bigl(1,\pi(y)/\pi(x)\bigr)$, and stays at $x$ if the proposal is rejected.
--
--   The theorem asserts three things about this chain: it is a genuine Markov chain (its transition matrix has nonnegative entries and rows summing to one); it satisfies the **detailed balance** equations $\pi(x)\,M(x,y)=\pi(y)\,M(y,x)$ for all states $x,y$, i.e. it is reversible with respect to $\pi$; and $\pi$ is a **stationary distribution** for it, meaning $\sum_x \pi(x)\,M(x,y)=\pi(y)$ for every $y$ — running the chain one step from $\pi$ returns $\pi$. This is the construction of §3.2.1 of Levin–Peres–Wilmer: a recipe turning any symmetric proposal mechanism into a chain with a prescribed stationary distribution.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 3.2.1, pp. 37-39

import Definitions.Def_mm_mcmc

namespace MarkovMixing

/-- **§3.2.1** (LPW): the Metropolis chain for a positive target distribution
`π` and a symmetric stochastic base chain `Ψ` is a Markov chain, reversible
with respect to `π`, with stationary distribution `π`. -/
theorem metropolis_stationary {V : Type*} [Fintype V] [DecidableEq V]
    (Ψ : Matrix V V ℝ) (hΨ : IsStochastic Ψ) (hsymm : ∀ x y : V, Ψ x y = Ψ y x)
    (π : V → ℝ) (hπ : IsDist π) (hpos : ∀ x : V, 0 < π x) :
    IsStochastic (metropolis Ψ π) ∧
    DetailedBalance (metropolis Ψ π) π ∧
    IsStationary (metropolis Ψ π) π := by
  sorry

end MarkovMixing
