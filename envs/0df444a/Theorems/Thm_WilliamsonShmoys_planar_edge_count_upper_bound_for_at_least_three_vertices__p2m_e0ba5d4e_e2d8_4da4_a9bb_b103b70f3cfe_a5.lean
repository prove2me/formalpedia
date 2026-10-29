-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_at_least_three_vertices__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_at_least_three_vertices__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:45:35.286411+00:00
-- url     : https://prove2.me/theorems/8d0b4468-66cb-492c-be3d-f60059245cd8
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This separates the upper-bound half of the target; a proof route derives it from Euler’s formula and face-degree bounds, with separate treatment of disconnected graphs and small components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_at_least_three_vertices__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    Q.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
