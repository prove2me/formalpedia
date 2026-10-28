-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- name    : WilliamsonShmoys.subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:07:53.686975+00:00
-- url     : https://prove2.me/theorems/30042ee0-6789-4cdd-b6ce-5bdbf951ce69
-- title:
--   Transfer an edge bound to a subgraph
-- statement:
--   A graph’s edge set is contained in its supergraph’s edge set, so the supergraph’s finite edge-count bound transfers to the subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_count_bound_39491eab_3342_47a8_bf1b_b037fb68e8e4
    {V : Type} [Fintype V]
    (H K : SimpleGraph V)
    (hHK : H ≤ K)
    (hK : K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
