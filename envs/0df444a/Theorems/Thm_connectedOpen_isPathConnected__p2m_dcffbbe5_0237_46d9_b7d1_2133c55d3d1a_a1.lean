-- Prove2me | Theorems.Thm_connectedOpen_isPathConnected__p2m_dcffbbe5_0237_46d9_b7d1_2133c55d3d1a_a1
-- name    : connectedOpen_isPathConnected__p2m_dcffbbe5_0237_46d9_b7d1_2133c55d3d1a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:33:55.895044+00:00
-- url     : https://prove2.me/theorems/5e3d82c8-779b-4c88-8979-881da8df90cb
-- title:
--   Connected open subsets of locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected open subset of a locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem connectedOpen_isPathConnected__p2m_dcffbbe5_0237_46d9_b7d1_2133c55d3d1a_a1 {X : Type} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by sorry
