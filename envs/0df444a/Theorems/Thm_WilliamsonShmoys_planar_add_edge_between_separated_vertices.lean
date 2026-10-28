-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_separated_vertices
-- name    : WilliamsonShmoys.planar_add_edge_between_separated_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T14:59:57.268987+00:00
-- url     : https://prove2.me/theorems/5da5ed27-eb9b-4ada-b452-3f499e7c3455
-- title:
--   Join separated vertices in a planar drawing
-- statement:
--   Given a drawing and two vertices in different components, extend the graph by an edge between them while preserving the drawing property and strictly increasing the edge count. This isolates the topological extension from selecting the vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_separated_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (u v : V)
    (hSeparated : ¬ H.Reachable u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        H.edgeSet.ncard < K.edgeSet.ncard := by sorry
