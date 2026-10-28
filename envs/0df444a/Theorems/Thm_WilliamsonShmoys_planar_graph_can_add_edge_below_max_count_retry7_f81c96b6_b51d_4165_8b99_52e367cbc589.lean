-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- name    : WilliamsonShmoys.planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T22:18:03.010186+00:00
-- url     : https://prove2.me/theorems/6bf923a0-d691-453f-9036-1546bc7e7b55
-- title:
--   A planar graph below the sharp count admits an edge augmentation
-- statement:
--   A graph on at least three vertices with the specified drawing and a strict deficit below `3|V| - 6` has a strictly larger planar supergraph on the same vertex type. This removes the edge-augmentation argument from the parent. A proof route is to prove that a drawing with no permissible added edge has triangular faces (with the needed component and boundary cases handled), which forces the sharp count; the strict deficit rules out that situation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_can_add_edge_below_max_count_retry7_f81c96b6_b51d_4165_8b99_52e367cbc589
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcount : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K ≠ H ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
