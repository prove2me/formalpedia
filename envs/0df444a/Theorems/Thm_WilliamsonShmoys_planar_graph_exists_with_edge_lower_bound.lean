-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_exists_with_edge_lower_bound
-- name    : WilliamsonShmoys.planar_graph_exists_with_edge_lower_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T23:44:54.042843+00:00
-- url     : https://prove2.me/theorems/a72c9f09-b91e-4837-995a-a64a8aa3adff
-- title:
--   A drawable graph with at least 3n − 6 edges exists on every finite ordered vertex set
-- statement:
--   For every finite linearly ordered vertex type with at least three vertices, there is a graph on that same type with a crossing-free drawing and at least 3n − 6 edges. A convex polygon boundary together with a fan triangulation supplies the graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_exists_with_edge_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, HasPlanarDrawingOn W ∧
      3 * Fintype.card V ≤ W.edgeSet.ncard + 6 := by sorry
