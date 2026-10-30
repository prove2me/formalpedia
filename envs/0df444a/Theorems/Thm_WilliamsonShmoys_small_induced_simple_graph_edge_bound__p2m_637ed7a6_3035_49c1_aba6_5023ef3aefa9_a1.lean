-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- name    : WilliamsonShmoys.small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:18:44.212213+00:00
-- url     : https://prove2.me/theorems/11b1833e-edb2-45e3-a964-4560a12d5a70
-- title:
--   Small induced simple graphs have few edges
-- statement:
--   For any subset of fewer than three vertices in a finite simple graph, the induced edge count is at most its cardinality minus one, with natural subtraction handling the empty subset.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_induced_simple_graph_edge_bound__p2m_637ed7a6_3035_49c1_aba6_5023ef3aefa9_a1
    {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V)
    (W : Finset V) (hW : W.card < 3) :
    (M.induce (W : Set V)).edgeSet.ncard ≤ W.card - 1 := by sorry
