-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_upper_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
-- name    : WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:25:42.894535+00:00
-- url     : https://prove2.me/theorems/1c01668a-0f94-4ae4-a554-8e823c9c0a96
-- title:
--   Edge upper bound for a drawable simple graph
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges. This isolates the Euler and face-degree argument from maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_edge_upper_bound__p2m_ec284709_a18f_4c8c_aa4a_41fee9be8d7b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    K.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  sorry
