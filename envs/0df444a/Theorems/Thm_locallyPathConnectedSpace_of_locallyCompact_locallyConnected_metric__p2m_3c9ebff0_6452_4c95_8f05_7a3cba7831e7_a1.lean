-- Prove2me | Theorems.Thm_locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_3c9ebff0_6452_4c95_8f05_7a3cba7831e7_a1
-- name    : locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_3c9ebff0_6452_4c95_8f05_7a3cba7831e7_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:40:33.048983+00:00
-- url     : https://prove2.me/theorems/11d97c0d-db05-4f06-93bb-b139682c8306
-- title:
--   Locally compact locally connected metric spaces are locally path-connected
-- statement:
--   Every locally compact, locally connected metric space is locally path-connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_3c9ebff0_6452_4c95_8f05_7a3cba7831e7_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
