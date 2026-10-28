-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound_2026
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound_2026
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:07:10.114291+00:00
-- url     : https://prove2.me/theorems/43f98bfb-7424-41c7-97de-56fe6ca417c5
-- title:
--   Planar simple graph edge bound
-- statement:
--   Every drawable simple graph on at least three vertices has at most 3|V| − 6 edges. This removes the upper-bound half of the target from the parent proof; it can be proved from Euler’s formula and face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound_2026
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
