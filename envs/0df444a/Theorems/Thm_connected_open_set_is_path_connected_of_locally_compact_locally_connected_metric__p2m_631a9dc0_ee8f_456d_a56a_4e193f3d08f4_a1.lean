-- Prove2me | Theorems.Thm_connected_open_set_is_path_connected_of_locally_compact_locally_connected_metric__p2m_631a9dc0_ee8f_456d_a56a_4e193f3d08f4_a1
-- name    : connected_open_set_is_path_connected_of_locally_compact_locally_connected_metric__p2m_631a9dc0_ee8f_456d_a56a_4e193f3d08f4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:46.032054+00:00
-- url     : https://prove2.me/theorems/c2a26abc-6385-42b5-9f97-cf4fff41f315
-- title:
--   Connected open subsets of locally compact locally connected metric spaces are path connected
-- statement:
--   Every connected open subset of a locally compact, locally connected metric space is path connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem connected_open_set_is_path_connected_of_locally_compact_locally_connected_metric__p2m_631a9dc0_ee8f_456d_a56a_4e193f3d08f4_a1
    {X : Type} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X]
    {U : Set X} (hU : IsOpen U) (hconn : IsConnected U) : IsPathConnected U := by
  sorry
