-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_ordered_unreachable_vertices
-- name    : WilliamsonShmoys.exists_ordered_unreachable_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:39:12.115713+00:00
-- url     : https://prove2.me/theorems/2bc0f464-ca11-442b-b3d3-e7ba023f2a6d
-- title:
--   A finite disconnected graph has an ordered unreachable pair
-- statement:
--   In a finite linearly ordered graph with at least three vertices, disconnectedness gives two vertices in different reachability classes, ordered so the first is less than the second.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_ordered_unreachable_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hGdisc : ¬ G.Connected) :
    ∃ u v : V, u < v ∧ ¬ G.Reachable u v := by sorry
