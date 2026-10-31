-- Prove2me | Theorems.Thm_isPathConnected_of_isConnected_isOpen_locallyCompact_locallyConnected_metric__p2m_074ba45e_42d9_4b53_93bb_86397c010941_a1
-- name    : isPathConnected_of_isConnected_isOpen_locallyCompact_locallyConnected_metric__p2m_074ba45e_42d9_4b53_93bb_86397c010941_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:25:49.146121+00:00
-- url     : https://prove2.me/theorems/3c9ebff0-6452-4c95-8f05-7a3cba7831e7
-- title:
--   Connected open subsets of locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected open subset of a locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem isPathConnected_of_isConnected_isOpen_locallyCompact_locallyConnected_metric__p2m_074ba45e_42d9_4b53_93bb_86397c010941_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by sorry
