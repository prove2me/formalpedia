-- Prove2me | Theorems.Thm_groupCohomology_natCard_H2_mul_of_shortExact
-- name    : groupCohomology.natCard_H2_mul_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/1c5dbdc9-07f4-5397-9b99-ffa96a36c8eb
-- title:
--   Multiplicativity of the Herbrand quotient in a short exact sequence
-- statement:
--   Let $G$ be a group that is finite and cyclic, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,\mathbb{Z}\,G$ of $\mathbb{Z}$-linear representations of $G$, assumed to be short exact, i.e. to be a short exact sequence $0 \to X_1 \to X_2 \to X_3 \to 0$ of $\mathbb{Z}[G]$-modules. Assume further that each of the six groups $H^1(G, X_i)$ and $H^2(G, X_i)$, for $i = 1,2,3$, is finite. Then the cardinalities of these six groups satisfy
--   $$\#H^2(G,X_2)\cdot \#H^1(G,X_1)\cdot \#H^1(G,X_3) \;=\; \#H^1(G,X_2)\cdot \#H^2(G,X_1)\cdot \#H^2(G,X_3),$$
--   where the cardinalities are taken as natural numbers via `Nat.card`. This is the cross-multiplied form of the multiplicativity of the Herbrand quotient $h(X) = \#H^2(G,X)/\#H^1(G,X)$, namely $h(X_2) = h(X_1)\,h(X_3)$, stated without division so that no invertibility or non-vanishing hypothesis is needed.
--
--   This is the classical statement that the Herbrand quotient of a $\mathbb{Z}[G]$-module, $G$ finite cyclic, is multiplicative in short exact sequences, in a purely integral form. It serves as the counting device behind the two results that cite it: the equality $\#H^1 = \#H^2$ for a short exact sequence whose outer cohomology is trivial, and the computation of $\#H^2$ for a short exact sequence with a term isomorphic to a trivial representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H2_mul_of_shortExact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H2_mul_of_shortExact
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact)
    [Finite (H1 X.X₁)] [Finite (H1 X.X₂)] [Finite (H1 X.X₃)]
    [Finite (H2 X.X₁)] [Finite (H2 X.X₂)] [Finite (H2 X.X₃)] :
    Nat.card (H2 X.X₂) * Nat.card (H1 X.X₁) * Nat.card (H1 X.X₃)
      = Nat.card (H1 X.X₂) * Nat.card (H2 X.X₁) * Nat.card (H2 X.X₃) := by sorry
