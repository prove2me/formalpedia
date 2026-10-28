-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- name    : WilliamsonShmoys.edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:05:23.162084+00:00
-- url     : https://prove2.me/theorems/6d1bfdba-e7f7-4c12-a293-ff43996cd691
-- title:
--   Monotonicity of finite simple-graph edge cardinality
-- statement:
--   On a finite vertex type, inclusion of simple graphs implies that the smaller graph's edge set has cardinality no greater than the larger graph's edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edgeSet_ncard_mono_cd050b01_9a07_4b9b_9132_918bb6a60ec5
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
