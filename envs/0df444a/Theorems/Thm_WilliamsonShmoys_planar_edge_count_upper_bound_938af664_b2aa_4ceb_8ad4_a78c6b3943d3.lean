-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:09:10.565996+00:00
-- url     : https://prove2.me/theorems/6592d8cf-da59-492a-a8f1-ee9bea53c09e
-- title:
--   Euler upper bound for planar graph edges
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound_938af664_b2aa_4ceb_8ad4_a78c6b3943d3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
