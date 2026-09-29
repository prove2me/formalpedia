-- Prove2me | Theorems.Thm_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
-- name    : groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6e99092d-ab40-5c6e-9242-6485ec6eab6c
-- title:
--   Order of H²(G,X₂) for an extension of ℤ
-- statement:
--   Let $G$ be a finite cyclic group and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\ \mathbb{Z}\ G$ of $\mathbb{Z}[G]$-modules, assumed short exact (`X.ShortExact`). Suppose given an isomorphism $e : X_3 \cong \mathbb{Z}$ onto the trivial representation `Rep.trivial ℤ G ℤ`, that $H^1(G,X_1)$ and $H^2(G,X_1)$ are finite with $\#H^1(G,X_1) = \#H^2(G,X_1)$, and that $H^1(G,X_2)$ is a subsingleton, i.e. vanishes. The conclusion is the conjunction: $H^2(G,X_2)$ is finite, and its cardinality equals the order of $G$, $\#H^2(G,X_2) = \#G$. Here $H^1$ and $H^2$ are Mathlib's group cohomology of a representation over $\mathbb{Z}$, and cardinalities are taken as `Nat.card`.
--
--   This is the algebraic skeleton of the cyclic second inequality in local class field theory, in the form giving equality: applied to $0 \to \mathcal{O}_L^\times \to L^\times \xrightarrow{v} \mathbb{Z} \to 0$ for a cyclic extension $L/K$ of local fields, with $H^1(G,L^\times) = 0$ by Hilbert 90 and the Herbrand quotient of the units equal to $1$, it yields $\#H^2(\mathrm{Gal}(L/K),L^\times) = [L:K]$. It is used in the computation of the order of $H^2$ for a multiplicative Galois action attached to a valuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H2_eq_natCard_of_shortExact_of_iso_trivial.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial
    {G : Type} [Group G] [Finite G] [IsCyclic G]
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (e : X.X₃ ≅ Rep.trivial ℤ G ℤ)
    [Finite (H1 X.X₁)] [Finite (H2 X.X₁)] (h1 : Nat.card (H1 X.X₁) = Nat.card (H2 X.X₁))
    [Subsingleton (H1 X.X₂)] :
    Finite (H2 X.X₂) ∧ Nat.card (H2 X.X₂) = Nat.card G := by sorry
