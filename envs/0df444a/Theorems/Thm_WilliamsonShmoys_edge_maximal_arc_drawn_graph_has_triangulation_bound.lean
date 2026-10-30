-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_arc_drawn_graph_has_triangulation_bound
-- name    : WilliamsonShmoys.edge_maximal_arc_drawn_graph_has_triangulation_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:20:41.755983+00:00
-- url     : https://prove2.me/theorems/b21952c5-cef5-45be-8330-15732a741057
-- title:
--   Edge bound for an edge-maximal arc-drawn graph
-- statement:
--   A drawable graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_maximal_arc_drawn_graph_has_triangulation_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by
  sorry
