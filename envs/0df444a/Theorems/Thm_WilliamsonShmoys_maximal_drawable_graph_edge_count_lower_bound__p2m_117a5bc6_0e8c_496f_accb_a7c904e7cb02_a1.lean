-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:38:18.665529+00:00
-- url     : https://prove2.me/theorems/c18646d9-4532-475f-9987-0b2cce81491a
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   A maximally drawable simple graph with at least three vertices has at least three times its vertex count minus six edges. The proof route is to show maximality forces a connected triangulated plane embedding, then apply Euler’s formula and count face-edge incidences. This handles the three-vertex boundary, where maximality yields the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_lower_bound__p2m_117a5bc6_0e8c_496f_accb_a7c904e7cb02_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → L = M)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by sorry
