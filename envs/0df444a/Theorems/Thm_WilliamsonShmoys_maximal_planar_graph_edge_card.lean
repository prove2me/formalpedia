-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_card
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_card
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T17:10:23.160578+00:00
-- url     : https://prove2.me/theorems/13d1a71c-b0e8-42ec-9f2b-0d1635c4724c
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal under planar edge additions, and has at least three vertices, has exactly three times its vertex count minus six edges. Prove this by formalizing the associated plane embedding, showing maximality makes every face triangular, and applying Euler’s formula and face-edge incidence counting. At three vertices, maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_graph_edge_card
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet ->
      WilliamsonShmoys.HasPlanarDrawingOn M ->
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 <= Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
