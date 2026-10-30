-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_supergraph
-- name    : WilliamsonShmoys.exists_triangulated_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:27:26.115818+00:00
-- url     : https://prove2.me/theorems/d25c82a0-710c-47eb-96b5-c257b11ac5d4
-- title:
--   Triangulated planar supergraph on the same vertices
-- statement:
--   Every connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex type whose edge count is exactly 3n−6. The conclusion also records edge-count monotonicity for the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulated_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hconn : ∀ u v : V, Nonempty (G.Walk u v)) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
