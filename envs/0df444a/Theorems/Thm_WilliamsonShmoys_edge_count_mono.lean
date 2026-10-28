-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_mono
-- name    : WilliamsonShmoys.edge_count_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:37:59.365164+00:00
-- url     : https://prove2.me/theorems/e6e6f3eb-5ed6-4950-8c28-8eada9671d20
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_mono {V : Type} [Fintype V] [LinearOrder V] (L H : SimpleGraph V) (hLH : L ≤ H) : L.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
