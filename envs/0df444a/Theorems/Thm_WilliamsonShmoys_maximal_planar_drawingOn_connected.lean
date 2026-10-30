-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected
-- name    : WilliamsonShmoys.maximal_planar_drawingOn_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T16:07:58.498733+00:00
-- url     : https://prove2.me/theorems/90599b14-5b71-48de-9bf9-85c7f1f2283c
-- title:
--   Maximal drawable graphs are connected
-- statement:
--   A graph on at least three vertices that is maximal among drawable supergraphs on its vertex type must be connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawingOn_connected
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hMax : ∀ K : SimpleGraph V,
      J ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ J)
    (hCard : 3 ≤ Fintype.card V) :
    J.Connected := by sorry
