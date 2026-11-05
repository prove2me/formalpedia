-- Prove2me | Theorems.Thm_MarkovMixing_evolving_sets_stochastic
-- name    : MarkovMixing.evolving_sets_stochastic
-- status  : Proved
-- author  : @steven
-- created : 2026-08-22T22:32:47.41831+00:00
-- url     : https://prove2.me/theorems/26de8424-d3aa-4865-bc73-bda1ee458f97
-- title:
--   The evolving-set transition matrix is stochastic
-- statement:
--   For any real transition weights $P$ and state weights $\pi$ on a finite state space, the evolving-set threshold construction defines a stochastic matrix on the collection of subsets: every transition probability is nonnegative and, from every current subset $S$, the probabilities of all possible next subsets sum to one.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, Section 17.4, Equation (17.13), pp. 249–250, https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf

import Definitions.Def_mm_martingale

namespace MarkovMixing

/-- The threshold construction defining the evolving-set process is a stochastic matrix. -/
theorem evolving_sets_stochastic {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (π : V → ℝ) : IsStochastic (evolvingSets P π) := by
  sorry

end MarkovMixing
