-- Prove2me | Theorems.Thm_Hirsch_q28_combinadic_unrank
-- name    : Hirsch.q28_combinadic_unrank
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T23:31:52.441326+00:00
-- url     : https://prove2.me/theorems/e7a0cd49-f147-4f36-8208-7a86ee00d832
-- title:
--   Combinadic unranking for the $Q_{28}$ chamber
-- statement:
--   Let $P\subset\mathbb{R}^5$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$. The $14$ nonnegative-chamber inequalities are indexed combinadically as strictly increasing $5$-tuples from $\{0,\ldots,13\}$.
--
--   This theorem records that the stored unranking map inverts combinadic rank on those tuples, and that those ranks lie in $\{0,\ldots,2001\}$.
--
--   **Formalization Note** The maps `unrank5` and `combRank` live in `Definitions.Def_Hirsch_q28_cert`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch
theorem q28_combinadic_unrank :
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry
end Hirsch
