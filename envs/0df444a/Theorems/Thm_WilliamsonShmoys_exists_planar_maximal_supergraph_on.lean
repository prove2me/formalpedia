-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_maximal_supergraph_on
-- name    : WilliamsonShmoys.exists_planar_maximal_supergraph_on
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:04:06.517951+00:00
-- url     : https://prove2.me/theorems/6f0daabb-7806-4f1d-8d5d-1f87b8cf2fd1
-- title:
--   Every finite planar drawing has a planar edge-maximal supergraph
-- statement:
--   A finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices for which every drawable supergraph has the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_maximal_supergraph_on
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K.edgeSet ⊆ H.edgeSet) := by sorry
