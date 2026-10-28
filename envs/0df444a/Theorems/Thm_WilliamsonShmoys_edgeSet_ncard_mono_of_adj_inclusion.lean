-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_adj_inclusion
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_of_adj_inclusion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T11:37:51.883469+00:00
-- url     : https://prove2.me/theorems/12a781ff-3a2b-4b49-a305-a6d9176fa821
-- title:
--   Edge count is monotone under adjacency inclusion
-- statement:
--   For finite simple graphs on the same vertex type, adjacency inclusion implies that the source graph’s edge-set cardinality is at most the target graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_mono_of_adj_inclusion
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
