-- Prove2me | Theorems.Thm_MarkovMixing_random_transpositions_lower
-- name    : MarkovMixing.random_transpositions_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:44:14.437262+00:00
-- url     : https://prove2.me/theorems/0d32039e-4c93-4b68-b93d-953e1c248984
-- title:
--   Proposition 8.11 -- random transpositions lower bound
-- statement:
--   The **random transpositions shuffle** of a deck of $n$ cards picks two cards independently and uniformly at random and swaps them: the identity is applied with probability $1/n$ and each transposition with probability $2/n^2$. Its stationary distribution is uniform. For a tolerance $\varepsilon$, the **mixing time** $t_{\mathrm{mix}}(\varepsilon)$ is the first $t$ at which $\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}\le\varepsilon$, where $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ is the total variation distance.
--
--   The theorem (Proposition 8.11 of Levin–Peres–Wilmer) asserts: for every $n\ge2$ and every $0<\varepsilon<1$,
--   $$t_{\mathrm{mix}}(\varepsilon)\;\ge\;\frac{n-1}{2}\,\log\!\Bigl(\frac{(1-\varepsilon)\,n}{6}\Bigr).$$
--   So order $\tfrac12\,n\log n$ shuffles are necessary. The obstruction is the number of **fixed points**: until almost every card has been touched at least once — a coupon-collector event taking $\tfrac12 n\log n$ pair draws — the deck has many more cards in their original position than a uniform ordering would.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 8.2.3, Proposition 8.11, p. 105

import Definitions.Def_mm_shuffle
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Proposition 8.11** (LPW): for the random transpositions chain on `n`
cards and `0 < ε < 1`,
`t_mix(ε) ≥ ((n−1)/2) log((1−ε)n/6)`. -/
theorem random_transpositions_lower (n : ℕ) (hn : 2 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ((n : ℝ) - 1) / 2 * Real.log ((1 - ε) * n / 6) ≤
      (mixingTime (randomTranspositions n)
        (uniformDist (Equiv.Perm (Fin n))) ε : ℝ) := by
  sorry

end MarkovMixing
