-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_planar_graph_has_extremal_edge_count
-- name    : WilliamsonShmoys.edge_maximal_planar_graph_has_extremal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:50:30.796358+00:00
-- url     : https://prove2.me/theorems/0fcfe75c-ca5c-4f44-b053-fab43bcb7554
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   An edge-maximal planar graph on at least three finite vertices has exactly 3|V|−6 edges. This supplies the geometric and counting conclusion needed after the finite extension step. A proof route is to show that any nontriangular face admits an added diagonal, so maximality forces a triangulation; connectedness and Euler’s formula then give the edge count. The hypothesis of at least three vertices is essential to this standard formula and is preserved explicitly.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_planar_graph_has_extremal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hY : HasPlanarDrawingOn Y)
    (hMax : forall Z : SimpleGraph V,
      HasPlanarDrawingOn Z ->
      (forall u v, Y.Adj u v -> Z.Adj u v) ->
      forall u v, Z.Adj u v -> Y.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    Y.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
