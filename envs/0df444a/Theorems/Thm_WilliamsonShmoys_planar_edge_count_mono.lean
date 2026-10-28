-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_mono
-- name    : WilliamsonShmoys.planar_edge_count_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:49:00.14774+00:00
-- url     : https://prove2.me/theorems/1f37eecd-ad63-4faf-9e87-08534f1dea3b
-- title:
--   Monotonicity of edge count
-- statement:
--   Inclusion of finite simple graphs on the same vertex type implies monotonicity of edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
