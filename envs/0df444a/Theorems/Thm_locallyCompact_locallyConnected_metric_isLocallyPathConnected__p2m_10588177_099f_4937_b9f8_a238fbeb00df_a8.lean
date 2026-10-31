-- Prove2me | Theorems.Thm_locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_10588177_099f_4937_b9f8_a238fbeb00df_a8
-- name    : locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_10588177_099f_4937_b9f8_a238fbeb00df_a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:23:36.385731+00:00
-- url     : https://prove2.me/theorems/c54d855c-94f6-4d86-936e-1e4be5e9169a
-- title:
--   Locally compact locally connected metric spaces are locally path connected
-- statement:
--   Every locally compact, locally connected metric space is locally path connected, without a global connectedness assumption.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyCompact_locallyConnected_metric_isLocallyPathConnected__p2m_10588177_099f_4937_b9f8_a238fbeb00df_a8 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
