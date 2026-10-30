-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_max_edge_euler_20261027
-- name    : WilliamsonShmoys.planar_drawing_max_edge_euler_20261027
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:48:59.310356+00:00
-- url     : https://prove2.me/theorems/938af664-b2aa-4ceb-8ad4-a78c6b3943d3
-- title:
--   Euler edge count for a maximum-edge drawable graph
-- statement:
--   A drawable graph on at least three vertices whose edge count is maximal among its drawable supergraphs has exactly three times the vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_max_edge_euler_20261027
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      M.edgeSet.ncard ≤ L.edgeSet.ncard) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
