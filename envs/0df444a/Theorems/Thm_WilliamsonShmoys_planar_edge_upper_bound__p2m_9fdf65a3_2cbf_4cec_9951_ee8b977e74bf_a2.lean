-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:11.581314+00:00
-- url     : https://prove2.me/theorems/71de413d-a2cb-43c4-9595-c6ba34d7c93b
-- title:
--   Planar edge upper bound for at least three vertices
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. The vertex-count hypothesis excludes the small cases that refuted the earlier unrestricted child. A proof can use Euler’s formula componentwise, accounting separately for components of size one and two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_9fdf65a3_2cbf_4cec_9951_ee8b977e74bf_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 <= Fintype.card V) : G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
