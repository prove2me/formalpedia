-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:16:37.004994+00:00
-- url     : https://prove2.me/theorems/85b28752-a0fb-4a56-8bde-69871f6bf21b
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound_fc016acd_24e0_4b4c_9f94_11715a39d633
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V)
    (hMax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L <= K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
