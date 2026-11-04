-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:29:08.068383+00:00
-- url     : https://prove2.me/theorems/126d21f0-5b15-4e81-98d4-afc1d569f5a6
-- title:
--   Edge count of a maximal connected drawable graph
-- statement:
--   A connected graph with at least three vertices that is maximal among graphs admitting the specified crossing-free drawing has exactly three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_6dc85c3d_85f5_4b78_a1c3_d13b079de4de_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) (hconn : N.Connected)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
