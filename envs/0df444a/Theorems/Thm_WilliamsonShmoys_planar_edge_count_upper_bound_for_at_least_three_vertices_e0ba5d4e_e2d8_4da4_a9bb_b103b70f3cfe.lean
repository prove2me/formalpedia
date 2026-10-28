-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_at_least_three_vertices_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_at_least_three_vertices_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:55:09.75968+00:00
-- url     : https://prove2.me/theorems/bade1508-4926-4dcc-ab69-3902a4ebf297
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. A proof route uses a plane embedding, Euler’s formula, face-degree bounds, and separate handling of components with fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_at_least_three_vertices_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    Q.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry
