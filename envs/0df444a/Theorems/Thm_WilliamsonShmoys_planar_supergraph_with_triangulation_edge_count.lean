-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_edge_count
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:58:28.356069+00:00
-- url     : https://prove2.me/theorems/c05799f7-3840-4d9c-911b-7f25f7b1541b
-- title:
--   Extend a planar drawing to the triangulation edge count
-- statement:
--   Every finite drawable simple graph on an ordered vertex type with at least three vertices has a drawable supergraph on the same vertex type with 3|V|−6 edges. This isolates the geometric completion and planar edge-count argument from the parent; maximality then forces the supergraph to equal the original graph. An independent proof route is to add noncrossing arcs inside faces until the drawing is triangulated, and combine Euler’s formula with face-edge incidence counting. The topological construction and count are the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_triangulation_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry
