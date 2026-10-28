-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_extremal_edge_count
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_extremal_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T04:51:22.835997+00:00
-- url     : https://prove2.me/theorems/a67a2052-6632-473c-9cb3-c2f0038d6e2e
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A globally maximal graph with a crossing-free drawing on at least three finite ordered vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_has_extremal_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hX : HasPlanarDrawingOn X)
    (hmax : forall Y : SimpleGraph V, HasPlanarDrawingOn Y ->
      (forall u v, X.Adj u v -> Y.Adj u v) ->
      forall u v, Y.Adj u v -> X.Adj u v)
    (hCard : 3 <= Fintype.card V) :
    X.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
