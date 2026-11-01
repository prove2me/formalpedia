-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1
-- name    : WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:09:36.06179+00:00
-- url     : https://prove2.me/theorems/9d5f7223-cd8c-4132-84b7-b2c8e47aeadb
-- title:
--   Planar supergraph edge lower bound
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with at least 3|V|−6 edges. One proof route augments the drawing to a triangulation and counts its faces and edges. This removes the geometric augmentation and planar counting work from the parent; applying the parent’s maximality hypothesis then identifies H with G. The unresolved core is proving the extension and count for the exact continuous-arc drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_supergraph_edge_bound__p2m_ab59570c_fffd_4137_a2d3_71557bc91725_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      (∀ u v, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by sorry
