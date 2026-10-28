-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_same_vertices_retry2_triangulation_extension
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_retry2_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:08:54.961987+00:00
-- url     : https://prove2.me/theorems/80347283-c5ef-4894-b09d-15da7aac39fd
-- title:
--   Finite maximal planar supergraph on the same vertices
-- statement:
--   A finite connected graph with the supplied planar drawing has a same-vertex planar supergraph whose edge count is at least that of every planar supergraph of it. The finite maximization argument gives the edge-maximal choice; connectedness is inherited from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_same_vertices_retry2_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConn : G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      ∀ K : SimpleGraph V,
        H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
