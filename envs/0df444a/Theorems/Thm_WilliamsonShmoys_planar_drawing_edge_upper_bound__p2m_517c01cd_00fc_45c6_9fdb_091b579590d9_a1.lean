-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:49:10.704998+00:00
-- url     : https://prove2.me/theorems/9bfb6b72-08dc-4057-9f94-78efbb45a4ca
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_517c01cd_00fc_45c6_9fdb_091b579590d9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 <= Fintype.card V) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry
