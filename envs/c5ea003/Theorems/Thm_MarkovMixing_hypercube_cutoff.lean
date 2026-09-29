-- Prove2me | Theorems.Thm_MarkovMixing_hypercube_cutoff
-- name    : MarkovMixing.hypercube_cutoff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T17:27:51.314544+00:00
-- url     : https://prove2.me/theorems/d7c2f6c8-5c41-46e3-b0ae-10adea6d9ed8
-- title:
--   Hypercube cutoff at $\frac12 n\log n$ with window $n$
-- statement:
--   The **lazy random walk on the $n$-dimensional hypercube** has state space $\{0,1\}^n$; at each step it stays put with probability $\tfrac12$ and otherwise flips a uniformly chosen coordinate. Its stationary distribution is uniform. Write $d_n(t)=\max_x\|P^t_n(x,\cdot)-\mathrm{unif}\|_{TV}$ for the worst-case total variation distance at time $t$ ($\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$). A family of chains has a **cutoff at $t_n$ with window $w_n$** when $w_n/t_n\to0$ and, evaluating the distance at times $t_n+\alpha w_n$,
--   $$\lim_{\alpha\to-\infty}\liminf_{n\to\infty}d_n\bigl(\lfloor t_n+\alpha w_n\rfloor\bigr)=1,\qquad\lim_{\alpha\to+\infty}\limsup_{n\to\infty}d_n\bigl(\lfloor t_n+\alpha w_n\rfloor\bigr)=0.$$
--
--   The theorem (Theorem 18.3 of Levin–Peres–Wilmer, the capstone of Chapter 18) asserts: the lazy hypercube walk has a cutoff at
--   $$t_n=\tfrac12\,n\log n\qquad\text{with window}\qquad w_n=n.$$
--
--   The walk's entire collapse from unmixed to mixed happens in a window of size $\Theta(n)$ around $\tfrac12n\log n$ — the sharpest form of the coupon-collector heuristic, since $\tfrac12n\log n$ is when the last slow coordinates get refreshed. The upper bound runs the spectral machinery of Mission VII through the walk's explicit eigenvalues $1-j/n$ (multiplicity $\binom nj$); the lower bound pushes the Hamming-weight distinguishing statistic of Mission IV to second-order precision. Historically this chain is where the cutoff phenomenon was first understood completely.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 18.2.2, Theorem 18.3, p. 251

import Definitions.Def_mm_cutoff
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Theorem 18.3** (LPW), the capstone of Chapter 18: the lazy random walk
on the `n`-dimensional hypercube has a cutoff at `(1/2) n log n` with a
window of size `n`. -/
theorem hypercube_cutoff :
    HasCutoffWindow (fun n => hypercubeWalk n)
      (fun n => uniformDist (Fin n → ZMod 2))
      (fun n => 2⁻¹ * n * Real.log n) (fun n => n) := by
  sorry

end MarkovMixing
