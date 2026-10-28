-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_new_adj
-- name    : WilliamsonShmoys.edgeSet_ncard_lt_of_new_adj
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T22:49:48.689899+00:00
-- url     : https://prove2.me/theorems/a1c2b1f4-dcbd-4055-9a5f-134a324b5bda
-- title:
--   A new adjacency strictly increases the finite edge count
-- statement:
--   If every edge of one finite simple graph is present in another and the latter has an adjacency missing from the former, then its edge set has strictly larger cardinality. This is the finite-set counting step independent of planarity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_lt_of_new_adj
    {V : Type} [Fintype V]
    (M N : SimpleGraph V)
    (hsub : ∀ u v, M.Adj u v → N.Adj u v)
    (u v : V)
    (hnew : N.Adj u v)
    (hmissing : ¬ M.Adj u v) :
    M.edgeSet.ncard < N.edgeSet.ncard := by sorry
