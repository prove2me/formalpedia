-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:03:19.337736+00:00
-- url     : https://prove2.me/theorems/9a318fe1-85ed-4677-94d2-01eeb5a6121d
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   A finite simple graph on at least three vertices with a crossing-free drawing has at most three times its vertex count minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_c924e691_b064_42cd_9f9f_84343d32d225_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
