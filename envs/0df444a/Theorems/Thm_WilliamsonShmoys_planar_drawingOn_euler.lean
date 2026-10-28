-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_euler
-- name    : WilliamsonShmoys.planar_drawingOn_euler
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:37:16.783829+00:00
-- url     : https://prove2.me/theorems/afa87191-145d-4a74-8c23-3dd7c454f185
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   A finite connected graph with the given crossing-free drawing has a face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_euler
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
