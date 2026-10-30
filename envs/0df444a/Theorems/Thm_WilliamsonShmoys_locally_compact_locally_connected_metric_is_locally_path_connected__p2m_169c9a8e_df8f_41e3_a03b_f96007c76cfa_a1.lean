-- Prove2me | Theorems.Thm_WilliamsonShmoys_locally_compact_locally_connected_metric_is_locally_path_connected__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
-- name    : WilliamsonShmoys.locally_compact_locally_connected_metric_is_locally_path_connected__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:51:00.333713+00:00
-- url     : https://prove2.me/theorems/631a9dc0-ee8f-456d-a56a-4e193f3d08f4
-- title:
--   Locally compact locally connected metric spaces are locally path connected
-- statement:
--   This supplies the local path connectedness missing from Mathlib’s open connected-set equivalence. The assumptions and conclusion are the standard criterion for locally compact locally connected metric spaces. A proof route is to use local compactness and local connectedness to construct sufficiently small connected neighborhoods with compact control, then apply the metric continuum theorem that connected locally connected compact pieces are arcwise connected to obtain path-connected neighborhood bases. This removes the ambient-topology work from the parent; that criterion is a remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.locally_compact_locally_connected_metric_is_locally_path_connected__p2m_169c9a8e_df8f_41e3_a03b_f96007c76cfa_a1 {X : Type} [MetricSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] : LocallyPathConnectedSpace X := by sorry
