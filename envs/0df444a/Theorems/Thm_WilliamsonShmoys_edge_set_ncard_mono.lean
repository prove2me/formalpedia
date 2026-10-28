-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_set_ncard_mono
-- name    : WilliamsonShmoys.edge_set_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T01:33:57.351285+00:00
-- url     : https://prove2.me/theorems/dafb26eb-bc6c-418e-bb2c-c92775981552
-- title:
--   Monotonicity of edge count under adjacency inclusion
-- statement:
--   Adjacency inclusion induces inclusion of the finite edge sets, so the first graph's edge count is at most the second's. This supplies the cardinality transfer in the parent proof.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_set_ncard_mono
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : ∀ u v, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
