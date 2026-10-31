-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:48:58.753007+00:00
-- url     : https://prove2.me/theorems/caae18f0-685f-4a93-b7e0-5fbdada5e71c
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1e4fc4c6_43c4_4ae0_af53_1d46a400a440_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) (hCard : 3 ≤ Fintype.card V) : N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
