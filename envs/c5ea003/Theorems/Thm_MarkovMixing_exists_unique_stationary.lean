-- Prove2me | Theorems.Thm_MarkovMixing_exists_unique_stationary
-- name    : MarkovMixing.exists_unique_stationary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:44:23.527997+00:00
-- url     : https://prove2.me/theorems/4d15376b-d91a-4c5d-a771-46c5570b25ca
-- title:
--   Corollary 1.17 -- existence and uniqueness of the stationary distribution
-- statement:
--   Every irreducible chain on a finite nonempty state space has exactly one stationary distribution: there exists a unique probability vector $\pi$ with $\pi P=\pi$. This is the goal theorem of the mission and the foundation of the whole Markov Chains and Mixing Times series.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 1.5.4, Corollary 1.17, p. 14

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Corollary 1.17** (LPW), the capstone of Chapter 1: an irreducible chain
on a finite state space has exactly one stationary distribution. -/
theorem exists_unique_stationary {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : Irreducible P) :
    ∃! π : V → ℝ, IsStationary P π := by
  sorry

end MarkovMixing
