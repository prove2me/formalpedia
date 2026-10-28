-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_separated_vertices_geometry
-- name    : WilliamsonShmoys.planar_add_edge_between_separated_vertices_geometry
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T15:18:02.656838+00:00
-- url     : https://prove2.me/theorems/005bebec-4750-4344-93f7-a812d7834e31
-- title:
--   Geometric extension by an edge between components
-- statement:
--   Extend the given crossing-free drawing by drawing an edge between two vertices in different connected components, while preserving all the packaged drawing conditions.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_add_edge_between_separated_vertices_geometry
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (u v : V)
    (hSeparated : ¬ H.Reachable u v)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
