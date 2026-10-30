-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:37:48.143819+00:00
-- url     : https://prove2.me/theorems/1591b9cd-ac13-4639-82d2-61e7ddbdd660
-- title:
--   Euler upper bound for a finite planar drawing
-- statement:
--   A simple graph with the specified crossing-free drawing and at least three vertices has at most 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_23341804_e9bd_4849_9be7_9e709bd142a9
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
