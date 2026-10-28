-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_exact_edge_count_upper_bound
-- name    : WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T18:10:37.342215+00:00
-- url     : https://prove2.me/theorems/8b190359-078d-4255-b82b-7f731a3703c6
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A graph with a drawing satisfying `HasPlanarDrawingOn` and at least three finite vertices has at most `3|V| − 6` edges, expressed without truncated subtraction. This removes the Euler-formula upper-bound argument from the parent. A proof route is to apply Euler’s formula to the drawing and use that every face boundary has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_exact_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
