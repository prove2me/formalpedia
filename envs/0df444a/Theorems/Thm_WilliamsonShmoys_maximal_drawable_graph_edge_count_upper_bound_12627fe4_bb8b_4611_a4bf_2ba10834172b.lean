-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:38:23.387924+00:00
-- url     : https://prove2.me/theorems/490f4a4f-03ed-4f9c-a0c5-a713a7cf09d0
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_upper_bound_12627fe4_bb8b_4611_a4bf_2ba10834172b
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
