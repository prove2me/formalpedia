-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_face_count
-- name    : WilliamsonShmoys.planar_drawingOn_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T17:52:52.002999+00:00
-- url     : https://prove2.me/theorems/6294dfb9-01c6-44e4-b6a8-a896c7d41add
-- title:
--   Euler and face-side bounds for a connected planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with a crossing-free drawing, there is a natural number of faces satisfying Euler’s formula and the face-boundary side count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn J)
    (hCard : 3 <= Fintype.card V)
    (hConnected : J.Connected) :
    ∃ f : ℕ,
      Fintype.card V + f = J.edgeSet.ncard + 2 ∧
      3 * f <= 2 * J.edgeSet.ncard := by sorry
