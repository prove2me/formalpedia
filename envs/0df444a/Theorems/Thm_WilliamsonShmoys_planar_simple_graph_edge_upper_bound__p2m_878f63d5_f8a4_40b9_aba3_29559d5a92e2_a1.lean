-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:52.401294+00:00
-- url     : https://prove2.me/theorems/34984a32-89db-4d2f-ac2e-84ee95aee4c9
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_878f63d5_f8a4_40b9_aba3_29559d5a92e2_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
