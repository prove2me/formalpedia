-- Prove2me | Theorems.Thm_MarkovMixing_cycle_eigenvalues
-- name    : MarkovMixing.cycle_eigenvalues
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T21:46:28.343546+00:00
-- url     : https://prove2.me/theorems/126b02d9-a9a0-45ce-80d0-b79aa29f9440
-- title:
--   Section 12.3.1 -- eigenvalues of the cycle
-- statement:
--   **Simple random walk on the $n$-cycle** is the Markov chain on $\mathbb Z_n=\{0,1,\dots,n-1\}$ that moves from $x$ to $x+1$ or $x-1\pmod n$ with probability $\tfrac12$ each. A real number $\lambda$ is an **eigenvalue** of the chain when there is a nonzero function $f:\mathbb Z_n\to\mathbb R$ with $Pf=\lambda f$, where $(Pf)(x)=\sum_yP(x,y)f(y)=\tfrac12f(x-1)+\tfrac12f(x+1)$.
--
--   The theorem (§12.3.1 of Levin–Peres–Wilmer) asserts: for $n\ge3$, every number of the form
--   $$\cos\Bigl(\frac{2\pi j}{n}\Bigr),\qquad j=0,1,\dots,n-1,$$
--   is an eigenvalue of the walk. The eigenfunctions behind these values are the discrete Fourier modes $x\mapsto\cos(2\pi jx/n)$ and $x\mapsto\sin(2\pi jx/n)$. (The statement exhibits these eigenvalues; that they exhaust the spectrum is not asserted.) In particular the spectral gap of the cycle is $1-\cos(2\pi/n)\approx2\pi^2/n^2$, giving relaxation time of order $n^2$ — the model computation for the spectral theory of Chapter 12, matching the coupling bounds for cycles obtained in earlier missions.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 12.3.1, pp. 156-157

import Definitions.Def_mm_spectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace MarkovMixing

/-- **§12.3.1** (LPW): the eigenvalues of simple random walk on the
`n`-cycle are `cos(2πj/n)` for `j = 0, 1, …, n−1`. -/
theorem cycle_eigenvalues (n : ℕ) [NeZero n] (hn : 3 ≤ n) (j : Fin n) :
    IsEigenvalue (cycleWalk n) (Real.cos (2 * Real.pi * j / n)) := by
  sorry

end MarkovMixing
