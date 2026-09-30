-- Prove2me | Theorems.Thm_Hirsch_q28_chamber_ranks_low
-- name    : Hirsch.q28_chamber_ranks_low
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T23:19:19.474134+00:00
-- url     : https://prove2.me/theorems/08bb4c4c-a2c4-4d39-b036-6badfd2bc645
-- title:
--   Low combinadic ranks of the $Q_{28}$ chamber certificate
-- statement:
--   Let $P\subset\mathbb{R}^5$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$. In the nonnegative chamber the $\binom{14}{5}=2002$ five-row subsystems are indexed by combinadic rank.
--
--   This theorem records the low-rank half of that enumeration: every rank in $\{0,\ldots,1099\}$ is accounted for by the stored singular, infeasible, or orbit tag; combinadic rank is inverted on strictly increasing $5$-tuples from $\{0,\ldots,13\}$; and those ranks lie in $\{0,\ldots,2001\}$.
--
--   **Formalization Note** The checkers live in `Definitions.Def_Hirsch_q28_cert`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch
theorem q28_chamber_ranks_low :
    (∀ r : ℕ, r < 1100 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry
end Hirsch
