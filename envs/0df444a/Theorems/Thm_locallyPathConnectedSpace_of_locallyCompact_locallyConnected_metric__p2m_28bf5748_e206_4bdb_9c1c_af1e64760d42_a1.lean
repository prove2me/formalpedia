-- Prove2me | Theorems.Thm_locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_28bf5748_e206_4bdb_9c1c_af1e64760d42_a1
-- name    : locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_28bf5748_e206_4bdb_9c1c_af1e64760d42_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:08:45.742042+00:00
-- url     : https://prove2.me/theorems/074ba45e-42d9-4b53-93bb-86397c010941
-- title:
--   Locally compact locally connected metric spaces are locally path connected
-- statement:
--   Every locally compact, locally connected metric space is locally path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyPathConnectedSpace_of_locallyCompact_locallyConnected_metric__p2m_28bf5748_e206_4bdb_9c1c_af1e64760d42_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
