-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1
-- name    : WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:00:13.938902+00:00
-- url     : https://prove2.me/theorems/bf2a6b94-c712-4371-81b2-f7600a9fcb4a
-- title:
--   Planar augmentation to a triangulated graph
-- statement:
--   Every graph with the specified planar drawing on a finite linearly ordered vertex type of size at least three has a drawable supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H) (hCard : 3 <= Fintype.card V) : ∃ K : SimpleGraph V, H <= K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ 3 * Fintype.card V - 6 = K.edgeSet.ncard := by sorry
