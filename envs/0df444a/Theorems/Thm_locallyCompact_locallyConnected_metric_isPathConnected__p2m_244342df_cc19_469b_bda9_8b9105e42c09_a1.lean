-- Prove2me | Theorems.Thm_locallyCompact_locallyConnected_metric_isPathConnected__p2m_244342df_cc19_469b_bda9_8b9105e42c09_a1
-- name    : locallyCompact_locallyConnected_metric_isPathConnected__p2m_244342df_cc19_469b_bda9_8b9105e42c09_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:58:50.423993+00:00
-- url     : https://prove2.me/theorems/0d5283b1-b9a0-466c-98c8-5f3339e20727
-- title:
--   Connected locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected, locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem locallyCompact_locallyConnected_metric_isPathConnected__p2m_244342df_cc19_469b_bda9_8b9105e42c09_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] [ConnectedSpace X] : PathConnectedSpace X := by sorry
