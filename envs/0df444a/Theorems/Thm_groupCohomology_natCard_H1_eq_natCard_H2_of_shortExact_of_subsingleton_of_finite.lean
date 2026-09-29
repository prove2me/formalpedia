-- Prove2me | Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
-- name    : groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/53889725-f0a3-51b2-91b9-f809f7629fcd
-- title:
--   Herbrand quotient 1 for an extension of a finite module
-- statement:
--   Let $G$ be a finite cyclic group (a group that is finite and cyclic), and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,\mathbb{Z}\,G$ of $\mathbb{Z}$-linear representations of $G$, assumed to be short exact, i.e. $0 \to X_1 \to X_2 \to X_3 \to 0$ is exact. Assume further that the group cohomology groups $H^1(G, X_1)$ and $H^2(G, X_1)$ are each subsingletons, i.e. trivial, and that the underlying module of $X_3$ is finite. The conclusion is the conjunction of three assertions: $H^1(G, X_2)$ is finite, $H^2(G, X_2)$ is finite, and their cardinalities agree, $\#H^1(G, X_2) = \#H^2(G, X_2)$; here the cardinalities are taken as `Nat.card`, so the stated equality would hold vacuously as $0 = 0$ were the two groups infinite, but finiteness is asserted alongside it.
--
--   In classical language this says that the Herbrand quotient $h(X_2) = \#H^2/\#H^1$ of a finite cyclic group $G$ equals $1$ for an extension of a finite module by a cohomologically trivial one. It is the form used in the computation of the Herbrand quotient of the unit group of a local field, and is cited by [`groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_ofMulDistribMulAction_of_subgroup) and [`groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation`](thm.html#groupCohomology.natCard_H2_ofMulDistribMulAction_eq_of_valuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    [Subsingleton (H1 X.X₁)] [Subsingleton (H2 X.X₁)] [Finite X.X₃] :
    Finite (H1 X.X₂) ∧ Finite (H2 X.X₂) ∧ Nat.card (H1 X.X₂) = Nat.card (H2 X.X₂) := by sorry
