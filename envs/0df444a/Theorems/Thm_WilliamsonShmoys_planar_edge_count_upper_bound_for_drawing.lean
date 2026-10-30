-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_drawing
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T19:06:38.301959+00:00
-- url     : https://prove2.me/theorems/11cac9c3-ffad-44bb-bc54-3f7ce46bd702
-- title:
--   Planar edge count upper bound for the supplied drawing predicate
-- statement:
--   A finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most three times its vertex count minus six edges. The boundary case of exactly three vertices is covered. A proof route is to treat components explicitly, then apply Euler’s formula and face-boundary counting to the drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
