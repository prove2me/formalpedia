-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulation_count
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulation_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:30:55.40741+00:00
-- url     : https://prove2.me/theorems/97eb0c0d-3af3-4155-856d-e9f9263e1640
-- title:
--   A drawable graph extends to one with the triangulation edge count
-- statement:
--   Every drawable simple graph on a finite ordered vertex type with at least three vertices has a drawable supergraph on the same vertices whose edge count is 3|V|−6. This packages planar edge augmentation to a triangulation together with the Euler-formula count. It is stronger than the target because it does not assume maximality of the input graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_triangulation_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V, G ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
