-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_planar_upper_bound
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_planar_upper_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:46:43.026304+00:00
-- url     : https://prove2.me/theorems/260c1c76-c6ab-4c8b-98b4-3919c8e114d9
-- title:
--   Planar simple graph edge upper bound
-- statement:
--   Any simple graph on at least three vertices with a crossing-free drawing has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_planar_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
