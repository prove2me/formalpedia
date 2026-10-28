-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- name    : WilliamsonShmoys.edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:48:10.596515+00:00
-- url     : https://prove2.me/theorems/acf2e904-e6f6-497c-b298-47f3b1956dd3
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   If L is a subgraph of T and T has exactly 3n−6 edges, then L has at most that many edges. This isolates the finite-set argument from the topology: graph inclusion gives edge-set inclusion, and cardinality is monotone for finite sets. The exact-count hypothesis already implies the requested inequality, so this child needs no separate n≥3 hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_monotone_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
    {V : Type} [Fintype V] [LinearOrder V]
    (L T : SimpleGraph V)
    (hLT : L ≤ T)
    (hT : T.edgeSet.ncard = 3 * Fintype.card V - 6) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
