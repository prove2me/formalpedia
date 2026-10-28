-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_bound_for_three_or_more_vertices_connect_components
-- name    : WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connect_components
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T07:35:03.110807+00:00
-- url     : https://prove2.me/theorems/6f722e78-c602-4d49-beb4-2dc55665e833
-- title:
--   Connect components of a finite planar drawing
-- statement:
--   A drawable finite simple graph with at least three vertices is contained in a connected drawable simple graph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_bound_for_three_or_more_vertices_connect_components
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ T : SimpleGraph V, L ≤ T ∧ T.Connected ∧ HasPlanarDrawingOn T := by sorry
