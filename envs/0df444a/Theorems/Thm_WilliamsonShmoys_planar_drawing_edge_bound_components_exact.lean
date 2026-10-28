-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_components_exact
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_components_exact
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:58:40.070814+00:00
-- url     : https://prove2.me/theorems/4db24ad1-8669-4807-8d3f-ffb0e29a5c1e
-- title:
--   Planar edge bound using the exact component count
-- statement:
--   A finite simple graph with a crossing-free drawing, at least three vertices, and at least two edges satisfies the component-sensitive planar edge bound using its actual connected-component count. A proof can apply the simple planar edge bound to components with at least three vertices and handle one- and two-vertex components separately. The global edge lower bound ensures the aggregate slack is at least three. This supplies the quantitative inequality needed after the exact-count Euler relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_components_exact
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hm : 2 ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 3 * Nat.card L.ConnectedComponent + 3 ≤
      3 * Fintype.card V := by sorry
