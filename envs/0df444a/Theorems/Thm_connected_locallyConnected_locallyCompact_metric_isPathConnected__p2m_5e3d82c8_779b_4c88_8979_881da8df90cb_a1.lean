-- Prove2me | Theorems.Thm_connected_locallyConnected_locallyCompact_metric_isPathConnected__p2m_5e3d82c8_779b_4c88_8979_881da8df90cb_a1
-- name    : connected_locallyConnected_locallyCompact_metric_isPathConnected__p2m_5e3d82c8_779b_4c88_8979_881da8df90cb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:39:44.799252+00:00
-- url     : https://prove2.me/theorems/8c678e95-a70a-4b1e-89ec-740d7b945156
-- title:
--   Connected locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected, locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem connected_locallyConnected_locallyCompact_metric_isPathConnected__p2m_5e3d82c8_779b_4c88_8979_881da8df90cb_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] [ConnectedSpace X] : PathConnectedSpace X := by sorry
