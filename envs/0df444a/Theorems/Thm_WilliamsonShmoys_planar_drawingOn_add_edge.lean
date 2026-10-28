-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_add_edge
-- name    : WilliamsonShmoys.planar_drawingOn_add_edge
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:27:51.941056+00:00
-- url     : https://prove2.me/theorems/0cba0cab-939f-4356-b54b-d750e753b3f6
-- title:
--   Draw an edge between two unreachable vertices
-- statement:
--   Given a finite planar drawing and distinct unreachable vertices, extend the graph to a planar-drawn supergraph that preserves old reachability and makes the selected vertices reachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_add_edge
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (u v : V)
    (huv : u ≠ v)
    (hnotReachable : ¬ P.Reachable u v) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (∀ x y, P.Reachable x y → Q.Reachable x y) ∧
      Q.Reachable u v := by sorry
