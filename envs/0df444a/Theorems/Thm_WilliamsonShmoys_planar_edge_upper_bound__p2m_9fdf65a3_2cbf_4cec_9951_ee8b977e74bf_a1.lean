-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T05:37:03.881635+00:00
-- url     : https://prove2.me/theorems/018f0253-429b-4f2d-9e37-b8496e9aae59
-- title:
--   Universal planar edge upper bound
-- statement:
--   Every finite simple graph with the given planar drawing has at most 3|V|−6 edges. This supplies the parent’s upper bound and does not require maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
