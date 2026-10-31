-- Prove2me | Theorems.Thm_connected_locallyCompact_locallyConnected_metric_pathConnected__p2m_c54d855c_94f6_4d86_936e_1e4be5e9169a_a1
-- name    : connected_locallyCompact_locallyConnected_metric_pathConnected__p2m_c54d855c_94f6_4d86_936e_1e4be5e9169a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:56.646053+00:00
-- url     : https://prove2.me/theorems/766fe75b-3114-46ee-9df3-df630ff681c5
-- title:
--   Connected locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected locally compact locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem connected_locallyCompact_locallyConnected_metric_pathConnected__p2m_c54d855c_94f6_4d86_936e_1e4be5e9169a_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] [ConnectedSpace X] : PathConnectedSpace X := by sorry
