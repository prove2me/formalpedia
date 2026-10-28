-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_of_tight_supergraph
-- name    : WilliamsonShmoys.edge_count_le_of_tight_supergraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:52:55.203371+00:00
-- url     : https://prove2.me/theorems/7006f004-7094-4053-9360-6482b51ba910
-- title:
--   Edge bound inherited from a tight supergraph
-- statement:
--   If a finite graph is a subgraph of a graph with exactly 3n−6 edges, then it has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_le_of_tight_supergraph
    {V : Type} [Fintype V] {G H : SimpleGraph V}
    (hGH : G ≤ H)
    (hHEq : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
