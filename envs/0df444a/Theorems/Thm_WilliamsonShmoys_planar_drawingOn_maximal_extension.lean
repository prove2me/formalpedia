-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_extension
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:46:07.887954+00:00
-- url     : https://prove2.me/theorems/7d7307a6-1e71-492f-893c-ada6bf603924
-- title:
--   Maximal planar drawing extension
-- statement:
--   Every graph with a planar drawing on a finite ordered vertex set has a drawing-preserving supergraph that is maximal among planar supergraphs on that same vertex set. The lower bound of three vertices is retained to match the target and the triangulation step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (H : SimpleGraph V), G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
