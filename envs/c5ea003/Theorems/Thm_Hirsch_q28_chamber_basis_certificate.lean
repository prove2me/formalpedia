-- Prove2me | Theorems.Thm_Hirsch_q28_chamber_basis_certificate
-- name    : Hirsch.q28_chamber_basis_certificate
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T23:05:18.323738+00:00
-- url     : https://prove2.me/theorems/b0e67752-022a-41ca-b026-4d247fe63787
-- title:
--   Chamber-basis completeness for the $Q_{28}$ certificate
-- statement:
--   Let $P\subset\mathbb{R}^5$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$. In the nonnegative chamber the description reduces to $14$ inequalities. The $\binom{14}{5}=2002$ five-row subsystems of that chamber are indexed by combinadic rank.
--
--   This theorem records three facts about that enumeration:
--
--   1. Every rank in $\{0,\ldots,2001\}$ is accounted for by the stored singular, infeasible, or orbit tag of the $Q_{28}$ certificate.
--   2. Combinadic rank is inverted by the stored unranking map on strictly increasing $5$-tuples from $\{0,\ldots,13\}$.
--   3. Those ranks lie in $\{0,\ldots,2001\}$.
--
--   This is the completeness statement for the chamber-basis half of the finite incidence certificate of $Q_{28}$.
--
--   **Formalization Note** The checkers `certOkUnrank`, `unrank5` and `combRank` are defined in `Definitions.Def_Hirsch_q28_cert`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table; polar/spindle language as in F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Section 2.2.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch
theorem q28_chamber_basis_certificate :
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry
end Hirsch
