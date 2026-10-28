-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_edge_bound
-- name    : WilliamsonShmoys.planar_triangulation_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T23:27:06.775162+00:00
-- url     : https://prove2.me/theorems/4d743ede-b8c7-489a-b312-50372e09b358
-- title:
--   A planar graph extends to the triangulation edge bound
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertices with at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := by sorry
