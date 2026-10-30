-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T04:36:48.061164+00:00
-- url     : https://prove2.me/theorems/dad39d86-4ed1-4b9b-930d-705a080f17ad
-- title:
--   Euler upper bound for a drawable simple graph
-- statement:
--   A finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_0576420d_0064_49d4_9582_204b47d32418
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
