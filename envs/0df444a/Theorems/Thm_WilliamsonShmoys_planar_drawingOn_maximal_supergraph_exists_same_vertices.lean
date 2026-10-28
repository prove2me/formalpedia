-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_exists_same_vertices
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T06:51:29.428075+00:00
-- url     : https://prove2.me/theorems/5eb029a2-9dbd-45ec-a820-37066936f459
-- title:
--   Existence of an edge-maximal planar supergraph on the same vertices
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion among graphs with such a drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph_exists_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn K ∧ G ≤ K ∧
      ∀ L : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn L →
        K ≤ L → L ≤ K := by sorry
