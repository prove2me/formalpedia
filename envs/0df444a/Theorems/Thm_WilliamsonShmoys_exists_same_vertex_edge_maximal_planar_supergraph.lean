-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_same_vertex_edge_maximal_planar_supergraph
-- name    : WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:09:45.796993+00:00
-- url     : https://prove2.me/theorems/390ba8de-e771-4970-b85e-b2c61ef8ac3f
-- title:
--   Existence of a maximal planar supergraph on the same vertices
-- statement:
--   A connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertex type that is maximal among planar supergraphs under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_same_vertex_edge_maximal_planar_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hconn : H.Connected) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
        ∀ K : SimpleGraph V, G ≤ K →
          WilliamsonShmoys.HasPlanarDrawingOn K → K = G := by sorry
