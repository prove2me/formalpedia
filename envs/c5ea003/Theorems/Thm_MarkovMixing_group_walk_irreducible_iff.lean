-- Prove2me | Theorems.Thm_MarkovMixing_group_walk_irreducible_iff
-- name    : MarkovMixing.group_walk_irreducible_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-21T01:43:17.097275+00:00
-- url     : https://prove2.me/theorems/fb3458c1-6c92-4e7a-a9d6-023e1a5b8f91
-- title:
--   Proposition 2.13 -- irreducibility of a group walk
-- statement:
--   The random walk on a finite group $G$ with increment distribution $\mu$ is irreducible if and only if the support $S=\{g:\mu(g)>0\}$ generates $G$.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 2.6.1, Proposition 2.13, p. 28

import Definitions.Def_mm_basic

namespace MarkovMixing

/-- **Proposition 2.13** (LPW): the random walk on a finite group with
increment distribution `μ` is irreducible if and only if the support of `μ`
generates the group. -/
theorem group_walk_irreducible_iff {G : Type*} [Group G] [Fintype G]
    [DecidableEq G] (μ : G → ℝ) (hμ : IsDist μ) :
    Irreducible (groupWalk μ) ↔ Subgroup.closure {g : G | 0 < μ g} = ⊤ := by
  sorry

end MarkovMixing
