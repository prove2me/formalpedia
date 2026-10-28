-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_extension_same_vertices
-- name    : WilliamsonShmoys.edge_maximal_planar_extension_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:38:01.536153+00:00
-- url     : https://prove2.me/theorems/9e0c65d1-d3ff-4650-b3e2-00ad918cb452
-- title:
--   A maximal planar extension on the same vertex type
-- statement:
--   Every graph with the given planar drawing has a planar supergraph on the same finite vertex type that is maximal in edge count among planar supergraphs of itself. Its edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_extension_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard <= H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard <= H.edgeSet.ncard := by sorry
