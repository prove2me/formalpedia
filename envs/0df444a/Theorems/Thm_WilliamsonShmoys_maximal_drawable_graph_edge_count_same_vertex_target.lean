-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_same_vertex_target
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_same_vertex_target
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:47:04.014998+00:00
-- url     : https://prove2.me/theorems/c7ea8b28-0253-489b-9e0e-3d033ae5b807
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_same_vertex_target
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K = N) :
    N.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
