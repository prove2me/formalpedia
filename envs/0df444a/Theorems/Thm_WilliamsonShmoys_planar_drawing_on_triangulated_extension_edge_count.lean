-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_triangulated_extension_edge_count
-- name    : WilliamsonShmoys.planar_drawing_on_triangulated_extension_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T16:09:08.258094+00:00
-- url     : https://prove2.me/theorems/14a7eb43-2f75-497f-b7e3-f014974cad08
-- title:
--   Planar completion with triangulated edge count
-- statement:
--   Any finite graph with a crossing-free drawing on at least three vertices has a planar supergraph on the same vertices whose edge count is 3|V|−6. This extends a planar graph to a triangulated planar graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_on_triangulated_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V, K ≤ L ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
