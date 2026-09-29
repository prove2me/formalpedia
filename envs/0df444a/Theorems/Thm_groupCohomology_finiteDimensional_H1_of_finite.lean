-- Prove2me | Theorems.Thm_groupCohomology_finiteDimensional_H1_of_finite
-- name    : groupCohomology.finiteDimensional_H1_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/eba34b31-ef88-5601-9b13-846ae0201180
-- title:
--   Finite-dimensionality of H¹(G,A) for finite G
-- statement:
--   Let $k$ be a field and $G$ a group, both taken in a fixed universe, with $G$ assumed finite, and let $A$ be an object of `Rep k G`, i.e. a $k$-linear representation of $G$, which is assumed to be finite-dimensional as a $k$-module. The assertion is that the first group cohomology `H1 A` — the Mathlib first cohomology module of the representation $A$, a $k$-module — is finite-dimensional over $k$. No further hypotheses are imposed: finiteness of $G$ and finite-dimensionality of the coefficient space are all that is required, and the conclusion is the typeclass statement `FiniteDimensional k (H1 A)` rather than an explicit bound on the dimension.
--
--   This is the elementary finiteness statement that group cohomology of a finite group in degree one with finite-dimensional coefficients is finite-dimensional, the cocycle space being a subspace of the space of all set-theoretic functions $G \to A$. It serves as the single-level input for finiteness results on inflation images and for the dimension inequalities used in the locally constant cohomology layer, being cited by [`groupCohomology.finiteDimensional_inflationImage`](thm.html#groupCohomology.finiteDimensional_inflationImage) and [`groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth`](thm.html#groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finiteDimensional_H1_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.finiteDimensional_H1_of_finite {k : Type u} [Field k] {G : Type u} [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A] :
    FiniteDimensional k (H1 A) := by sorry
