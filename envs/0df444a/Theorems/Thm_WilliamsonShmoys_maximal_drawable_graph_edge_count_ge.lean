-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_edge_count_ge
-- name    : WilliamsonShmoys.maximal_drawable_graph_edge_count_ge
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T04:02:16.475702+00:00
-- url     : https://prove2.me/theorems/376c689f-e3ac-4106-8acc-4f7a2eed72d0
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal graph with a crossing-free planar drawing on at least three finite vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_graph_edge_count_ge
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : forall Q : SimpleGraph V,
      (forall {u v}, P.Adj u v -> Q.Adj u v) ->
      WilliamsonShmoys.HasPlanarDrawingOn Q -> Q = P)
    (hV : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= P.edgeSet.ncard := by sorry
