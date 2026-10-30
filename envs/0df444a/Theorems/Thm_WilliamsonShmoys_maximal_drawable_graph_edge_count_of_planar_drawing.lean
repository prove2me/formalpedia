-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_of_planar_drawing
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_of_planar_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T03:48:29.090583+00:00
-- url     : https://prove2.me/theorems/7c2588ab-cf8b-4df4-aa88-bc43ffc13337
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three finite vertices has exactly `3|V| − 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_of_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P)
    (hV : 3 <= Fintype.card V) :
    P.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
