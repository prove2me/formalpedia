-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:54.261281+00:00
-- url     : https://prove2.me/theorems/b086cf8e-feab-4218-a571-b7d2828fd0cf
-- title:
--   Lower edge bound for an edge-maximal planar graph
-- statement:
--   A finite edge-maximal graph with the specified planar drawing and at least three vertices has at least 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_planar_graph_edge_count_lower_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) (hmax : forall L : SimpleGraph V, (forall {u v : V}, K.Adj u v -> L.Adj u v) -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) : 3 * Fintype.card V - 6 <= K.edgeSet.ncard := by sorry
