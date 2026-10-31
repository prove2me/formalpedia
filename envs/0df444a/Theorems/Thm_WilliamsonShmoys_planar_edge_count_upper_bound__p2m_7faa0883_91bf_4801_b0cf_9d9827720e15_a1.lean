-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:04:57.96605+00:00
-- url     : https://prove2.me/theorems/c61a4fef-10c9-4ef4-8d71-ebe38bea863d
-- title:
--   Planar edge-count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n−6 edges. This isolates the Euler-formula upper-bound argument from maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hDraw : HasPlanarDrawingOn L) : L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
