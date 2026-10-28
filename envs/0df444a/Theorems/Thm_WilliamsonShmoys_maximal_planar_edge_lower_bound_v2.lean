-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_v2
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T13:50:57.800222+00:00
-- url     : https://prove2.me/theorems/088c0741-8213-4581-bb95-81433ddb1982
-- title:
--   Maximal planar edge lower bound
-- statement:
--   A drawable graph with at least three vertices that has no proper drawable supergraph on the same vertex set has at least three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_v2 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : HasPlanarDrawingOn L) (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L) (hcard : 3 ≤ Fintype.card V) : 3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
