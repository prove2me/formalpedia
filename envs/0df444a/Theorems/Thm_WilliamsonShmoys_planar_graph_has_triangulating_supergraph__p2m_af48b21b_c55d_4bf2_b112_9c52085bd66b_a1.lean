-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1
-- name    : WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:37:06.81036+00:00
-- url     : https://prove2.me/theorems/5e849ad0-992f-4795-a8f1-d28ee483fe3d
-- title:
--   Every finite drawable planar graph has a triangulating supergraph
-- statement:
--   Every drawable finite simple planar graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges. A planar embedding can be augmented by noncrossing diagonals to a triangulation, and Euler’s formula gives its edge count. The parent applies maximality to show this supergraph is the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_has_triangulating_supergraph__p2m_af48b21b_c55d_4bf2_b112_9c52085bd66b_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
