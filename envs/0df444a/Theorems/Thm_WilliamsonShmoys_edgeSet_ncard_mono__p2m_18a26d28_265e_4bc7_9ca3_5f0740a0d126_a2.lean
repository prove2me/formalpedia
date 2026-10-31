-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:47:12.641823+00:00
-- url     : https://prove2.me/theorems/c8cb92f0-7b8e-4243-b121-8e27ed12e88c
-- title:
--   Monotonicity of edge count under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_18a26d28_265e_4bc7_9ca3_5f0740a0d126_a2 {V : Type} [Fintype V] [LinearOrder V] (X Y : SimpleGraph V) (hXY : X ≤ Y) : X.edgeSet.ncard ≤ Y.edgeSet.ncard := by sorry
