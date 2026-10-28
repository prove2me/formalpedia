-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_for_edge_bound_v2
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_for_edge_bound_v2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:39:18.080531+00:00
-- url     : https://prove2.me/theorems/f6f43d9c-1a42-4393-873f-4f1dc292284e
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite simple graphs on the same vertex type, inclusion of adjacency relations implies monotonicity of edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono_for_edge_bound_v2 {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (h : G ≤ K) : G.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
