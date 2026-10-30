-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:08:26.228599+00:00
-- url     : https://prove2.me/theorems/7f070797-9c8c-4920-a9a1-c5ca93c4daed
-- title:
--   Planar edge count upper bound for the packaged drawing predicate
-- statement:
--   A finite simple graph with a crossing-free drawing as defined by HasPlanarDrawingOn and at least three vertices has at most three times its number of vertices minus six edges. The boundary hypothesis excludes the small cases where this bound need not hold.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_3cb48610_7a77_41d9_a56e_df3f423e0d25
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V)
    (hRdraw : WilliamsonShmoys.HasPlanarDrawingOn R)
    (hCard : 3 ≤ Fintype.card V) :
    R.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
