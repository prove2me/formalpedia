-- Prove2me | Theorems.Thm_WilliamsonShmoys_le_of_edgeSet_ncard_le_of_le
-- name    : WilliamsonShmoys.le_of_edgeSet_ncard_le_of_le
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T12:45:30.567339+00:00
-- url     : https://prove2.me/theorems/adb71c60-2206-4cc5-be47-66fa6d2b631c
-- title:
--   Finite edge count and inclusion give reverse inclusion
-- statement:
--   For graphs on a finite vertex type, if one is a subgraph of the other and has no more edges, then the reverse subgraph inclusion also holds.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.le_of_edgeSet_ncard_le_of_le
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    H ≤ G := by sorry
