-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:41:27.237327+00:00
-- url     : https://prove2.me/theorems/3e7d9d46-6410-4d53-b22b-599f73e58841
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_5ef2fec7_c68a_4083_8ca2_c9c55a373b08_a2 {V : Type} [Fintype V] [LinearOrder V] (W : SimpleGraph V) (hW : WilliamsonShmoys.HasPlanarDrawingOn W) (hV : 3 ≤ Fintype.card V) : W.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
