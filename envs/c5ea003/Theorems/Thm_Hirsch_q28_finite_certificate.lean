-- Prove2me | Theorems.Thm_Hirsch_q28_finite_certificate
-- name    : Hirsch.q28_finite_certificate
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T22:59:52.574685+00:00
-- url     : https://prove2.me/theorems/a155ac83-7cc5-403d-85c1-2e609cefd15a
-- title:
--   Finite sign-orbit certificate for the $Q_{28}$ polar
-- statement:
--   Let $P\subset\mathbb{R}^5$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$, described by the $28$ inequalities $\langle a_i,x\rangle\le 1$. Independent sign changes of the first four coordinates partition the vertices of $P$ into $20$ orbits. The stored integer tables of the $Q_{28}$ certificate equip this quotient with an integer potential, taking the value $0$ at the positive apex orbit and $6$ at the negative apex orbit.
--
--   This theorem records the finite incidence facts of that certificate:
--
--   1. If two signed orbit representatives have at least four original inequalities tight at both, then their orbit labels are equal or form an edge of the quotient graph.
--   2. If two orbit labels have potential differing by more than one, then every pair of signed representatives has at most three common original actives.
--   3. Every quotient edge changes the potential by at most one.
--   4. The stored tightness bit of a signed representative is equivalent to the corresponding integer inner product equalling the orbit denominator.
--   5. Every combinadic rank in $\{0,\ldots,2001\}$ is accounted for by the stored singular, infeasible, or orbit tag.
--   6. Combinadic rank is inverted by the stored unranking map on strictly increasing $5$-tuples from $\{0,\ldots,13\}$.
--   7. Those ranks lie in $\{0,\ldots,2001\}$.
--
--   These are the exact combinatorial contents used to bound the width of $Q_{28}$ in Corollary 2.9 of Matschke, Santos and Weibel.
--
--   **Formalization Note** The lookup tables and checkers are defined in `Definitions.Def_Hirsch_q28_cert`. This theorem asserts that those checkers hold, not the geometric identification of Euclidean vertices with the stored orbits.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table; polar/spindle language as in F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Section 2.2.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem q28_finite_certificate :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) ∧
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by sorry
end Hirsch
