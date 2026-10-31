-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:38:48.416286+00:00
-- url     : https://prove2.me/theorems/758453e2-af8f-402e-8f99-cb077a45819a
-- title:
--   Upper edge bound for a finite planar simple graph
-- statement:
--   Every finite simple graph with the specified planar drawing and at least three vertices has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound__p2m_cf44c216_3f6e_4f0d_9ff9_4dc3d94f14d1_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hV : 3 <= Fintype.card V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
