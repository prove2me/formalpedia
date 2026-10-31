-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- name    : WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:11:00.787733+00:00
-- url     : https://prove2.me/theorems/40bf128a-95fa-481c-8fd2-3c8143f624ef
-- title:
--   Simple planar edge bound
-- statement:
--   A drawable simple graph on at least three vertices has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_simple_edge_bound__p2m_bdf730fd_a18a_4f08_870b_a5969b01342b_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) : M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
