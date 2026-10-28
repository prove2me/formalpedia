-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_supergraph
-- name    : WilliamsonShmoys.planar_drawing_triangulation_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T01:56:45.291487+00:00
-- url     : https://prove2.me/theorems/cb6e5cb3-1f07-40f8-8769-776d2b0867d1
-- title:
--   A planar drawing extends to a triangulation
-- statement:
--   Every graph with the specified crossing-free drawing on a finite ordered vertex type of size at least three has a planar supergraph on the same vertex type with exactly 3|V|−6 edges. The parent applies maximality to identify this supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ T : SimpleGraph V,
      G ≤ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
