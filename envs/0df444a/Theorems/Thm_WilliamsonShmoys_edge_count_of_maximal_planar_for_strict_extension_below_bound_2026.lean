-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_for_strict_extension_below_bound_2026
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_for_strict_extension_below_bound_2026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:49:15.403504+00:00
-- url     : https://prove2.me/theorems/9bb7d70f-683c-4443-a5cd-72660326da80
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no strict drawable supergraph on the same vertices has exactly `3 * |V| - 6` edges. This supplies the extremal count needed by the parent. The independent proof route is to use maximality to show the drawing is connected and every face is triangular, then combine Euler's formula with the face-edge incidence count. The hypothesis `|V| ≥ 3` is essential for this formula; at the boundary `|V| = 3`, maximality gives the triangle with three edges. Establishing these facts for the supplied arc-based drawing definition is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_for_strict_extension_below_bound_2026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, K ≤ H → HasPlanarDrawingOn H → H = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
