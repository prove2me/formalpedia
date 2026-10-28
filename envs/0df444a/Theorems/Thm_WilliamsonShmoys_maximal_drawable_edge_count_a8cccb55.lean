-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_a8cccb55
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_a8cccb55
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:37:38.348138+00:00
-- url     : https://prove2.me/theorems/e16e5e2a-3898-48bd-8d7a-134b8268654c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no proper drawable supergraph on the same vertices has exactly 3|V|−6 edges. For the standard proof route, use the drawing to show the graph is connected and every face is bounded by a triangle: otherwise an edge can be added inside a face while preserving a planar drawing, contradicting maximality. Apply Euler’s formula and count each triangular face along its three boundary edges, with each edge incident to two faces. For |V|=3 this gives three edges. This removes the planar-topology and Euler-count step from the parent. The remaining core obligation is to formalize faces and edge augmentation from the packaged continuous-arc drawing predicate, then derive the count without assuming an embedding structure absent from that predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_a8cccb55
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ X : SimpleGraph V,
      U ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
