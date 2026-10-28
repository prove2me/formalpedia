-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_mono_of_adj_inclusion
-- name    : WilliamsonShmoys.edge_card_mono_of_adj_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T23:57:04.90516+00:00
-- url     : https://prove2.me/theorems/d54dc3b4-1e95-4718-bf12-6eb3b2ba71a8
-- title:
--   Edge count is monotone under adjacency inclusion
-- statement:
--   If every edge of one finite simple graph is also an edge of another graph on the same vertex type, then the first graph has no more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_mono_of_adj_inclusion
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hAdj : forall u v, G.Adj u v -> H.Adj u v) :
    G.edgeSet.ncard <= H.edgeSet.ncard := by sorry
