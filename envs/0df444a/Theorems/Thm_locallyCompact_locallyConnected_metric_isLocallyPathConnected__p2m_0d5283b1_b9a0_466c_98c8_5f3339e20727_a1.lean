-- Prove2me | Theorems.Thm_locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_0d5283b1_b9a0_466c_98c8_5f3339e20727_a1
-- name    : locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_0d5283b1_b9a0_466c_98c8_5f3339e20727_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:15:20.562783+00:00
-- url     : https://prove2.me/theorems/70e80337-b866-4721-97ce-c1fcd2237ffb
-- title:
--   Locally compact locally connected metric spaces are locally path connected
-- statement:
--   Every locally compact, locally connected metric space is locally path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_0d5283b1_b9a0_466c_98c8_5f3339e20727_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
