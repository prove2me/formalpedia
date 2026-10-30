-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_35554814_repair3
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_35554814_repair3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:56:01.722026+00:00
-- url     : https://prove2.me/theorems/e0551cff-2896-4403-b2e0-e8fa37e927b2
-- title:
--   Planar simple graph edge-count upper bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most `3|V| − 6` edges. Derive a planar embedding from the arc drawing, connect components in the plane if needed, and apply Euler’s formula and face-edge incidence counting. This isolates the general upper-bound argument from maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_35554814_repair3
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P) :
    P.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
