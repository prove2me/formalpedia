-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_formula
-- name    : WilliamsonShmoys.planar_drawing_euler_formula
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:53:24.104995+00:00
-- url     : https://prove2.me/theorems/6571165c-6bc8-4592-a4bf-b8a7b4511fe9
-- title:
--   Euler formula for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing satisfies Euler’s formula for some natural-number face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_euler_formula
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ f : ℕ, G.edgeSet.ncard + 2 = Fintype.card V + f := by sorry
