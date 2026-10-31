-- Prove2me | Theorems.Thm_connected_open_set_is_path_connected__p2m_fa27784c_dacd_4815_954d_f281325d7eb3_a1
-- name    : connected_open_set_is_path_connected__p2m_fa27784c_dacd_4815_954d_f281325d7eb3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:54:20.401956+00:00
-- url     : https://prove2.me/theorems/28bf5748-e206-4bdb-9c1c-af1e64760d42
-- title:
--   Connected open subsets are path connected in locally compact locally connected metric spaces
-- statement:
--   Every connected open subset of a locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem connected_open_set_is_path_connected__p2m_fa27784c_dacd_4815_954d_f281325d7eb3_a1 {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] (U : Set X) (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by sorry
