-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_density_below_bound_v3
-- name    : WilliamsonShmoys.edge_maximal_planar_density_below_bound_v3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:51:47.228803+00:00
-- url     : https://prove2.me/theorems/8233e9d7-ff90-44df-80fb-d5b30ed530a0
-- title:
--   Density of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is maximal among drawable supergraphs has at least `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_density_below_bound_v3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hKmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
