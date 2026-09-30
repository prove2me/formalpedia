-- Prove2me | Theorems.Thm_Hirsch_q28_polar_orbit_identification
-- name    : Hirsch.q28_polar_orbit_identification
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-05T22:59:25.368212+00:00
-- url     : https://prove2.me/theorems/acb543ac-87e2-4553-a386-abd7e2a7e712
-- title:
--   Vertices of the $Q_{28}$ polar are the stored sign-orbits
-- statement:
--   Let $P=\{x\in\mathbb{R}^5:\langle a_i,x\rangle\le 1,\ i=1,\ldots,28\}$ be the polar of the Matschke--Santos--Weibel prismatoid $Q_{28}$, with apices $u=e_5$ and $v=-e_5$. Write $\mathrm{flip}_s$ for the coordinatewise sign change of the first four coordinates encoded by a $4$-bit pattern $s$, and write $p_o$ for the stored nonnegative representative of orbit $o$.
--
--   Every Euclidean extreme point of $P$ is of the form $\mathrm{flip}_s(p_o)$ for some orbit label $o$ and sign pattern $s$. If two extreme points span an extreme segment of $P$, then their orbit labels are equal or form an edge of the stored quotient graph. The orbit label of an extreme point is unique. Moreover $u$ (resp. $v$) is the unsigned representative of orbit $1$ (resp. $0$), and every sign-flip of those two orbits recovers the corresponding apex.
--
--   This is the geometric bridge from the H-polytope $P$ to the finite sign-orbit certificate of $Q_{28}$. Combined with the $1$-Lipschitz potential on the quotient, it forbids a padded walk of length $3$ between the two apex links.
--
--   **Formalization Note** `orbitPoint` and `flipPoint` are the maps $p_o$ and $\mathrm{flip}_s$ from `Definitions.Def_Hirsch_q28_cert`. Adjacency is the extreme-segment predicate `Adj` of the Hirsch model.
-- source:
--   B. Matschke, F. Santos, C. Weibel, The width of five-dimensional prismatoids, Proc. London Math. Soc. 110 (2015) 647-672, arXiv:1202.4701, Corollary 2.9 and the explicit $Q_{28}$ vertex table; polar/spindle language as in F. Santos, A counterexample to the Hirsch conjecture, Ann. of Math. 176 (2012) 383-412, arXiv:1006.2814, Section 2.2.

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Hirsch

namespace Hirsch
theorem q28_polar_orbit_identification :
    (∀ x : EuclideanSpace ℝ (Fin 5),
      x ∈ extremePoints ℝ (Hpoly q28A q28B) →
        ∃ o : Fin 20, ∃ s : Fin 16, x = flipPoint s (orbitPoint o)) ∧
    (∀ x y : EuclideanSpace ℝ (Fin 5),
      Adj (Hpoly q28A q28B) x y →
        ∃ o1 o2 : Fin 20, ∃ s1 s2 : Fin 16,
          x = flipPoint s1 (orbitPoint o1) ∧
          y = flipPoint s2 (orbitPoint o2) ∧
          (o1 = o2 ∨ QuotientAdj o1 o2)) ∧
    (∀ x : EuclideanSpace ℝ (Fin 5), ∀ o1 o2 : Fin 20, ∀ s1 s2 : Fin 16,
      x = flipPoint s1 (orbitPoint o1) →
      x = flipPoint s2 (orbitPoint o2) → o1 = o2) ∧
    q28U = flipPoint 0 (orbitPoint 1) ∧
    q28V = flipPoint 0 (orbitPoint 0) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 1) = q28U) ∧
    (∀ s : Fin 16, flipPoint s (orbitPoint 0) = q28V) := by sorry
end Hirsch
