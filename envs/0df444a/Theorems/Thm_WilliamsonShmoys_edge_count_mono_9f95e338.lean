-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono_9f95e338
-- name    : WilliamsonShmoys.edge_count_mono_9f95e338
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:03:08.261329+00:00
-- url     : https://prove2.me/theorems/5de4fe5b-7925-447a-9a62-658182799582
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies that the edge count is monotone. Prove this by deriving inclusion of edge sets and applying finite-set cardinality monotonicity. This supplies the counting step used by the parent independently of the drawing hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono_9f95e338
    {V : Type} [Fintype V] (H T : SimpleGraph V) (hsub : H ≤ T) :
    H.edgeSet.ncard ≤ T.edgeSet.ncard := by
  sorry
