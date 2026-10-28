-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawn_simple_graph_edge_bound
-- name    : WilliamsonShmoys.maximal_drawn_simple_graph_edge_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T06:49:10.92699+00:00
-- url     : https://prove2.me/theorems/43f223d8-0144-4339-8232-053458d3fe91
-- title:
--   Euler edge bound for a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that has no drawable proper supergraph on the same vertex type has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawn_simple_graph_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
