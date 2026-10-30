-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_for_triangulation_extension_v2_0463fea4
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_for_triangulation_extension_v2_0463fea4
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:14:06.289044+00:00
-- url     : https://prove2.me/theorems/988c2725-6106-44e5-9793-243ea2dd6303
-- title:
--   Planar edge upper bound for triangulation extension
-- statement:
--   Every drawable finite simple graph with at least three vertices has at most `3|V| - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_for_triangulation_extension_v2_0463fea4
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hR : WilliamsonShmoys.HasPlanarDrawingOn R) :
    R.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
