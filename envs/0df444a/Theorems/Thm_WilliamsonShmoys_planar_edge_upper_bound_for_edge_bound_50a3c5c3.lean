-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound_for_edge_bound_50a3c5c3
-- name    : WilliamsonShmoys.planar_edge_upper_bound_for_edge_bound_50a3c5c3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:55:55.827638+00:00
-- url     : https://prove2.me/theorems/3ad36388-d6fa-41eb-b98d-0a94f59970e4
-- title:
--   Planar edge upper bound for the edge-count theorem
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three has at most `3n − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound_for_edge_bound_50a3c5c3
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hCard : 3 ≤ Fintype.card V) :
    Q.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
