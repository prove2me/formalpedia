-- Prove2me | Theorems.Thm_MarkovMixing_adjacent_transpositions_upper
-- name    : MarkovMixing.adjacent_transpositions_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:44:51.34899+00:00
-- url     : https://prove2.me/theorems/7641945f-2df2-4973-a7d8-837a8d65a04d
-- title:
--   Section 16.1.2 -- adjacent transpositions upper bound
-- statement:
--   The **lazy random adjacent transpositions shuffle** of a deck of $n$ cards does nothing with probability $\tfrac12$ and otherwise swaps the cards in a uniformly chosen pair of neighbouring positions $(i,i+1)$: the identity carries probability $\tfrac12$ and each of the $n-1$ adjacent transpositions probability $1/\bigl(2(n-1)\bigr)$. Its stationary distribution is uniform over orderings. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ with $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (§16.1.2, display (16.4) of Levin–Peres–Wilmer) asserts: for every $0<\varepsilon<1$ there is an $N$ such that for all $n\ge N$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\le\;2\,n^3\log_2 n.$$
--   Moving cards only between neighbouring positions is slow — order $n^3\log n$ steps suffice (and, by the companion lower bound, order $n^3$ steps are necessary). The book's proof couples the shuffle with a simpler process through a comparison of Dirichlet forms.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 16.1.2, Eq. (16.4), pp. 218-219

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace MarkovMixing

/-- **§16.1.2, Eq. (16.4)** (LPW): for the lazy random adjacent
transpositions shuffle on `n` cards and any `0 < ε < 1`, for sufficiently
large `n`, `t_mix(ε) ≤ 2 n³ log₂ n`. -/
theorem adjacent_transpositions_upper (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (mixingTime (groupWalk (adjacentTranspositionDist n))
        (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) ≤
        2 * (n : ℝ) ^ 3 * Real.logb 2 n := by
  sorry

end MarkovMixing
