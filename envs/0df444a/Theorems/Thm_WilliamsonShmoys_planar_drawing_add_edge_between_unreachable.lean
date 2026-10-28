-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_unreachable
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_unreachable
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T12:11:52.901704+00:00
-- url     : https://prove2.me/theorems/677c186b-e8ac-4249-b519-9c589f2312a1
-- title:
--   Add an edge between components while preserving a planar drawing
-- statement:
--   If two vertices of a finite ordered graph are in different connected components and the graph has a crossing-free drawing, one can add the edge between those vertices and still obtain a crossing-free drawing on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_unreachable
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G < H ∧ H.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
