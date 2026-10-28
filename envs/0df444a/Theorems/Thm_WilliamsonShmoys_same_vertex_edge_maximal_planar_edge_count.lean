-- Prove2me | Theorems.Thm_WilliamsonShmoys_same_vertex_edge_maximal_planar_edge_count
-- name    : WilliamsonShmoys.same_vertex_edge_maximal_planar_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:10:27.903516+00:00
-- url     : https://prove2.me/theorems/2f796d8e-0e3d-4ce8-adf2-6f937e56381d
-- title:
--   Edge count of a maximal planar graph on a fixed vertex type
-- statement:
--   An inclusion-maximal simple planar graph on a finite linearly ordered vertex type with at least three vertices has exactly three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.same_vertex_edge_maximal_planar_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = G) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
