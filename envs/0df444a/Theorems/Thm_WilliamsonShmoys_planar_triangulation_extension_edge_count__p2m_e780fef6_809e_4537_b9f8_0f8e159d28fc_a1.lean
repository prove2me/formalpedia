-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:26.41999+00:00
-- url     : https://prove2.me/theorems/70a8b6e0-c40a-44e8-9147-f9396a2e926b
-- title:
--   Triangulation completion with exact planar edge count
-- statement:
--   Every finite graph with a crossing-free drawing on at least three fixed vertices has a drawable supergraph on the same vertex set whose edge count plus six equals three times the number of vertices. This isolates the topological augmentation and Euler-counting work; the parent applies maximality to identify this completion with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension_edge_count__p2m_e780fef6_809e_4537_b9f8_0f8e159d28fc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
