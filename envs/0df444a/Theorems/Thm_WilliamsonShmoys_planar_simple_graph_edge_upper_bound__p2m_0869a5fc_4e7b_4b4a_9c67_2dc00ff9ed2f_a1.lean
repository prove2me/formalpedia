-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
-- name    : WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:44.153464+00:00
-- url     : https://prove2.me/theorems/fbee940c-de84-434e-86ab-bbeb9fbfb2ac
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any finite simple graph on at least three vertices that has the specified planar drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_upper_bound__p2m_0869a5fc_4e7b_4b4a_9c67_2dc00ff9ed2f_a1 {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V) (hU : HasPlanarDrawingOn U)
    (hV : 3 ≤ Fintype.card V) :
    U.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
