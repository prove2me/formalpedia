-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:43:49.913871+00:00
-- url     : https://prove2.me/theorems/77204b41-0c73-44c4-9bf9-908d2902df70
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any finite simple graph with at least three vertices that has the specified crossing-free drawing has at most 3|V|−6 edges. This is the Euler-formula upper bound, independent of maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_d113e12d_71ad_41a3_b6a2_eff564f35d28_a1 {V : Type} [Fintype V] [LinearOrder V] (Q : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn Q) : Q.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
