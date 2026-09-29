-- Prove2me | Theorems.Thm_MarkovMixing_top_to_random_lower_bound
-- name    : MarkovMixing.top_to_random_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T20:25:50.48366+00:00
-- url     : https://prove2.me/theorems/8907a2cd-c14d-4234-a54b-a45be187b347
-- title:
--   Proposition 7.14 -- lower bound for the top-to-random shuffle
-- statement:
--   Consider the **top-to-random shuffle** of a deck of $n$ cards: at each step the top card is reinserted at a uniformly random position. Its stationary distribution is uniform over orderings. Write $P^t(x,\cdot)$ for the law of the deck after $t$ shuffles from the ordering $x$, $\|\mu-\nu\|_{TV}=\max_A|\mu(A)-\nu(A)|$ for the total variation distance, and $d(t)=\max_x\|P^t(x,\cdot)-\mathrm{unif}\|_{TV}$.
--
--   The theorem (Proposition 7.14 of Levin–Peres–Wilmer) asserts: for every $\varepsilon>0$ there is an $\alpha_0>0$ such that for every $\alpha>\alpha_0$ there is an $N$ with: for all $n\ge N$ and every integer time
--   $$t\;\le\;n\log n-\alpha n,\qquad\text{one has}\qquad d(t)\;\ge\;1-\varepsilon.$$
--   Slightly before time $n\log n$ the deck is still nearly maximally far from uniform. The witness event is the relative order of the cards originally near the bottom, which the shuffle has not yet touched. Together with the matching upper bound of Mission III, this exhibits the abrupt transition (cutoff) of the top-to-random shuffle at $n\log n$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 7.4.2, Proposition 7.14, pp. 96-97

import Definitions.Def_mm_lower
import Definitions.Def_mm_stopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace MarkovMixing

/-- **Proposition 7.14** (LPW): for the top-to-random shuffle on `n` cards,
for every `ε > 0` there is an `α₀` such that for `α > α₀` and all
sufficiently large `n`, `d(n log n − α n) ≥ 1 − ε`. -/
theorem top_to_random_lower_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ α : ℝ, α₀ < α → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℕ, (t : ℝ) ≤ n * Real.log n - α * n →
        1 - ε ≤ distStationary (topToRandom n)
          (uniformDist (Equiv.Perm (Fin n))) t := by
  sorry

end MarkovMixing
