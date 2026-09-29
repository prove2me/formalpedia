-- Prove2me | Theorems.Thm_MarkovMixing_heat_kernel_spectral_bound
-- name    : MarkovMixing.heat_kernel_spectral_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:39:54.530288+00:00
-- url     : https://prove2.me/theorems/88cb5863-fec2-40f2-bdb3-aea1d8b697a4
-- title:
--   Heat-kernel spectral bound $|H_t(x,y)-\pi(y)|\le\sqrt{\pi(y)/\pi(x)}\,e^{-\gamma t}$
-- statement:
--   Let $P$ be an irreducible Markov chain on a finite state space $V$ with stationary distribution $\pi$, reversible with respect to it (detailed balance: $\pi(x)P(x,y)=\pi(y)P(y,x)$). The **heat kernel** at real time $t\ge0$ is $H_t(x,y)=\sum_ke^{-t}\tfrac{t^k}{k!}P^k(x,y)$ — the continuous-time chain driven by a rate-one Poisson clock. Among the eigenvalues of $P$ (real $\lambda$ with $Pf=\lambda f$ for some nonzero $f$), $\lambda_2$ is the largest eigenvalue different from $1$, and $\gamma=1-\lambda_2$ is the **spectral gap** (Mission VII).
--
--   The theorem (Theorem 20.6 of Levin–Peres–Wilmer) asserts the pointwise estimate: for all states $x,y$ and all $t\ge0$,
--   $$\bigl|H_t(x,y)-\pi(y)\bigr|\;\le\;\sqrt{\frac{\pi(y)}{\pi(x)}}\;e^{-\gamma t}.$$
--
--   In continuous time the convergence rate is governed by the spectral gap $\gamma$ itself — not the absolute gap $\gamma_\star$ of the discrete theory: negative eigenvalues, which cause the discrete chain to oscillate, are killed by the Poisson smoothing, since $P$'s eigenvalue $\lambda$ becomes $e^{-(1-\lambda)t}$ for the heat kernel. The prefactor $\sqrt{\pi(y)/\pi(x)}$ comes from expanding the transition kernel in the $\ell^2(\pi)$-orthonormal eigenbasis of Mission VII's spectral representation. This estimate is the continuous-time engine behind the product-chain theorem of this mission.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 20.3, Theorem 20.6, Eq. (20.10), p. 268

import Definitions.Def_mm_continuous
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace MarkovMixing

/-- **Theorem 20.6** (LPW): for a reversible irreducible chain with spectral
gap `γ`, the heat kernel satisfies
`|H_t(x,y) − π(y)| ≤ √(π(y)/π(x)) e^{-γt}`. -/
theorem heat_kernel_spectral_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (P : Matrix V V ℝ) (hP : IsStochastic P)
    (hirr : Irreducible P) (π : V → ℝ) (hπ : IsStationary P π)
    (hrev : DetailedBalance P π) (x y : V) (t : ℝ) (ht : 0 ≤ t) :
    |heatKernel P t x y - π y| ≤
      Real.sqrt (π y / π x) * Real.exp (-(spectralGap P) * t) := by
  sorry

end MarkovMixing
