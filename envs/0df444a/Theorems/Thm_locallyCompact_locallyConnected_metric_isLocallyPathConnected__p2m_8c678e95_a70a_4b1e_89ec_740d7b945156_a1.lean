-- Prove2me | Theorems.Thm_locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_8c678e95_a70a_4b1e_89ec_740d7b945156_a1
-- name    : locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_8c678e95_a70a_4b1e_89ec_740d7b945156_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:48:18.800574+00:00
-- url     : https://prove2.me/theorems/244342df-cc19-469b-bda9-8b9105e42c09
-- title:
--   Local path connectedness of connected locally compact locally connected metric spaces
-- statement:
--   A connected, locally compact, locally connected metric space is locally path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_8c678e95_a70a_4b1e_89ec_740d7b945156_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] [ConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
