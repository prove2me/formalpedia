-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:31:33.66984+00:00
-- url     : https://prove2.me/theorems/5e162297-64c4-47bc-a15b-f2485c67d65d
-- title:
--   Euler upper bound for planar graph edge count
-- statement:
--   Every graph with a planar drawing on at least three vertices has at most 3|V| − 6 edges. This bound does not require maximality or connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_count_upper_bound_repair_8fa97b2b
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
