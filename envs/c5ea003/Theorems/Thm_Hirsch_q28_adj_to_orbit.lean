-- Prove2me | Theorems.Thm_Hirsch_q28_adj_to_orbit
-- name    : Hirsch.q28_adj_to_orbit
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-06T00:12:04.822315+00:00
-- url     : https://prove2.me/theorems/7774f952-9af5-4c79-a48b-52e585b695c1
-- title:
--   Adjacency on the $Q_{28}$ polar descends to the stored quotient
-- statement:
--   Let $P$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$. An extreme segment of $P$ joins two signed orbit representatives whose orbit labels are equal or form an edge of the stored quotient graph $\mathrm{QuotientAdj}$.
--
--   The argument uses that adjacency forces at least four common original active inequalities, together with the stored pairwise common-active cardinalities of signed representatives.
--
--   **Formalization Note** Adjacency is the extreme-segment predicate `Adj` of the Hirsch model. The orbit labels are those of `Hirsch.q28_extreme_classification`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table; polar/spindle language as in F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Section 2.2.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem q28_adj_to_orbit :
    ∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2) := by sorry
end Hirsch
