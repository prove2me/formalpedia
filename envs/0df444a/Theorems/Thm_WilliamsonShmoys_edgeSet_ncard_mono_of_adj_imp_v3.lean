-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_of_adj_imp_v3
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_of_adj_imp_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:54:17.116169+00:00
-- url     : https://prove2.me/theorems/d76da6f8-0d46-43cd-8366-006b912f4c72
-- title:
--   Monotonicity of edge count under adjacency inclusion
-- statement:
--   If each adjacency in a finite simple graph is also an adjacency in another graph on the same vertex type, the first graph’s edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_of_adj_imp_v3
    {V : Type} [Fintype V] [DecidableEq V]
    (N M : SimpleGraph V)
    (hsub : ∀ u v, N.Adj u v → M.Adj u v) :
    N.edgeSet.ncard ≤ M.edgeSet.ncard := by sorry
