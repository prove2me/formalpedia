-- Prove2me | Theorems.Thm_locallyCompact_locallyConnected_metric_locallyPathConnected__p2m_766fe75b_3114_46ee_9df3_df630ff681c5_a1
-- name    : locallyCompact_locallyConnected_metric_locallyPathConnected__p2m_766fe75b_3114_46ee_9df3_df630ff681c5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:39:37.022981+00:00
-- url     : https://prove2.me/theorems/fa27784c-dacd-4815-954d-f281325d7eb3
-- title:
--   Locally compact locally connected metric spaces are locally path connected
-- statement:
--   Every locally compact, locally connected metric space has a basis of path-connected neighborhoods at each point.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyCompact_locallyConnected_metric_locallyPathConnected__p2m_766fe75b_3114_46ee_9df3_df630ff681c5_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
