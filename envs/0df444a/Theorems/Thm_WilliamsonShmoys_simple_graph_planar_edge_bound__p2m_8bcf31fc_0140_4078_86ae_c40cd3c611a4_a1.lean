-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1
-- name    : WilliamsonShmoys.simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:28:16.268483+00:00
-- url     : https://prove2.me/theorems/ddf70dfc-9e43-42b2-878d-a461f3516711
-- title:
--   Edge bound for a finite simple planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges. The result does not require maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simple_graph_planar_edge_bound__p2m_8bcf31fc_0140_4078_86ae_c40cd3c611a4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel H.Adj := Classical.decRel _
     H.edgeFinset.card + 6 <= 3 * Fintype.card V) := by sorry
