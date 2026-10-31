-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:23:20.247988+00:00
-- url     : https://prove2.me/theorems/adaa59b8-bbaf-4393-8e55-4a0450b92ec8
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3n−6 edges. This is the Euler planar edge bound; one proof route is to handle connected components and apply Euler’s formula after triangulating faces, with the simple-graph condition excluding faces of length one or two in the relevant counting argument. The cardinality threshold is essential to this standard bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_84f2d88d_c1bb_48f4_b85d_8d668d11d624_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
