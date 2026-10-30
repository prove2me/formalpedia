-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:27:30.727158+00:00
-- url     : https://prove2.me/theorems/e1d36954-e3fe-4560-a783-a7db2e32f709
-- title:
--   Planar graph edge count upper bound
-- statement:
--   Every finite simple graph with a drawing satisfying the packaged planar drawing predicate and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7a2d1b0a_59f6_4246_bb02_8a4c93f926fa_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hCard : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) : G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
