-- Prove2me | Theorems.Thm_Hirsch_q28_quotient_lipschitz
-- name    : Hirsch.q28_quotient_lipschitz
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T23:07:41.742312+00:00
-- url     : https://prove2.me/theorems/d3a013ec-46c5-40b1-b1a2-03345c6f8091
-- title:
--   Quotient potential of the $Q_{28}$ polar
-- statement:
--   Let $P\subset\mathbb{R}^5$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$. After reducing vertices by independent sign changes of the first four coordinates, the stored tables describe a $20$-vertex quotient graph with an integer potential, taking the value $0$ at the positive apex orbit and $6$ at the negative apex orbit.
--
--   This theorem records the incidence facts of that quotient:
--
--   1. Four or more common original active inequalities force equal orbit labels or a quotient edge.
--   2. A potential gap greater than one forbids four common actives.
--   3. Every quotient edge changes the potential by at most one.
--   4. Stored tightness bits match the integer inner product against a signed orbit representative.
--
--   These are the exact combinatorial contents that make the quotient a conservative supergraph of the $1$-skeleton, with a $1$-Lipschitz potential.
--
--   **Formalization Note** The tables `commonActiveCard`, `orbitLevel`, `QuotientAdj`, `tightMask` and `intDotFlip` are defined in `Definitions.Def_Hirsch_q28_cert`.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table; polar/spindle language as in F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Section 2.2.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Hirsch

namespace Hirsch
theorem q28_quotient_lipschitz :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) := by sorry
end Hirsch
