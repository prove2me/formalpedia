-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_of_exact_supergraph_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- name    : WilliamsonShmoys.subgraph_edge_count_of_exact_supergraph_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:43:17.302197+00:00
-- url     : https://prove2.me/theorems/a9144690-12c8-41e9-930d-139d854f98e7
-- title:
--   Edge bound passes to subgraphs
-- statement:
--   If a finite simple graph is a subgraph of a graph on the same vertex type with exactly 3n − 6 edges, then it also has at most 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_count_of_exact_supergraph_bound_b9b806f7_2f7a_4d09_923b_24ccea114a12
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcount : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
