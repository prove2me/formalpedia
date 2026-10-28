-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_subgraph
-- name    : WilliamsonShmoys.planar_drawingOn_subgraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T11:27:00.064465+00:00
-- url     : https://prove2.me/theorems/3428c325-3d7b-4f19-a6d5-5b38e722d19d
-- title:
--   Planar drawing restricts to a subgraph
-- statement:
--   A graph on the same vertices that is a subgraph of a graph with the supplied crossing-free drawing inherits such a drawing by reusing the vertex locations and arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_subgraph
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V} (hGH : G ≤ H)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    WilliamsonShmoys.HasPlanarDrawingOn G := by sorry
