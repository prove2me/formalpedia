-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_maximal_extension
-- name    : WilliamsonShmoys.planar_drawing_edge_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:52:08.335814+00:00
-- url     : https://prove2.me/theorems/737e05e2-778d-4a4a-b6f9-30991c6bcc82
-- title:
--   Extend a planar drawing to an edge maximal planar supergraph
-- statement:
--   Every finite planar graph on at least three vertices has a planar supergraph on the same vertices whose edge count is at least the original's and is maximal among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V,
        (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard) := by sorry
