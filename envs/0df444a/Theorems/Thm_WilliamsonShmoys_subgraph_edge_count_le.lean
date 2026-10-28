-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_edge_count_le
-- name    : WilliamsonShmoys.subgraph_edge_count_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T21:40:55.09876+00:00
-- url     : https://prove2.me/theorems/f3a48bc5-00a6-4407-b33e-a0c48c264eb3
-- title:
--   Subgraph edge count monotonicity
-- statement:
--   A subgraph on a finite vertex type has no more edges than its supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.subgraph_edge_count_le
    {V : Type} [Fintype V] (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
