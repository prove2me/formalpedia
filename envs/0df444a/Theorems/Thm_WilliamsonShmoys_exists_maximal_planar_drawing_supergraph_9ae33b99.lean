-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_drawing_supergraph_9ae33b99
-- name    : WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_9ae33b99
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:17:33.534199+00:00
-- url     : https://prove2.me/theorems/5af7ce4a-fbd6-4449-b2e6-8dd383cc21fe
-- title:
--   Extend a planar drawing to an inclusion-maximal planar supergraph
-- statement:
--   For any finite graph with a crossing-free drawing, there is a planar supergraph on the same vertex type whose edge set is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_drawing_supergraph_9ae33b99
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K = H := by sorry
