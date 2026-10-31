-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- name    : WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:08:55.230596+00:00
-- url     : https://prove2.me/theorems/808b4142-3aa4-463f-be5d-a7d43b832047
-- title:
--   Euler upper bound for a finite planar graph
-- statement:
--   Every finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_count_upper_bound__p2m_dbe5418d_e2f2_4868_ba95_7b9be2d245d0_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
