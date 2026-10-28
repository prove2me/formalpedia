-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_add_edge_geometry
-- name    : WilliamsonShmoys.planar_drawingOn_add_edge_geometry
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T13:44:57.300565+00:00
-- url     : https://prove2.me/theorems/412cb47a-76a2-44cf-8ea3-7bbffdce5ead
-- title:
--   Extend a planar drawing by an edge between components
-- statement:
--   Given a finite graph drawing and distinct vertices in different connected components, there is a planar-drawn supergraph that retains the old graph and adds an edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_add_edge_geometry
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (u v : V)
    (huv : u ≠ v)
    (hnotReachable : ¬ P.Reachable u v) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Adj u v := by sorry
