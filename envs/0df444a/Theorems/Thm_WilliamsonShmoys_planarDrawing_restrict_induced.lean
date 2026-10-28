-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_restrict_induced
-- name    : WilliamsonShmoys.planarDrawing_restrict_induced
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T18:03:45.743995+00:00
-- url     : https://prove2.me/theorems/0259ef47-d0d8-4592-b159-f74137f25fa2
-- title:
--   Restrict a planar drawing to an induced subgraph
-- statement:
--   Any induced subgraph of a graph with a planar drawing inherits a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawing_restrict_induced
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (S : Finset V) :
    WilliamsonShmoys.HasPlanarDrawingOn (G.induce (↑S : Set V)) := by sorry
