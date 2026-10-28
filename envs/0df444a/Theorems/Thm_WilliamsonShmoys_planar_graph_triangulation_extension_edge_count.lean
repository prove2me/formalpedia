-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_extension_edge_count
-- name    : WilliamsonShmoys.planar_graph_triangulation_extension_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:45:26.59752+00:00
-- url     : https://prove2.me/theorems/d839d705-6fcc-4c88-b277-9f84682e1a8e
-- title:
--   Planar spanning extension with triangulation edge count
-- statement:
--   Every finite graph with a crossing-free drawing and at least three vertices has a planar extension on the same vertex type whose edge count is 3|V|−6. This removes the planar augmentation and Euler-counting work from the parent; the parent uses maximality to show that extension equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_triangulation_extension_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
