-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_mono
-- name    : WilliamsonShmoys.planar_drawing_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:04:38.740069+00:00
-- url     : https://prove2.me/theorems/85a9685f-0cc5-4dce-9223-5f4001137b6b
-- title:
--   Planar drawing is preserved by deleting edges
-- statement:
--   Any subgraph obtained by deleting edges from a graph with a crossing-free drawing has a crossing-free drawing on the same vertex type, using the same vertex locations and edge arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_mono
    {V : Type} [Fintype V] [LinearOrder V]
    {A B : SimpleGraph V}
    (hAB : A ≤ B)
    (hB : WilliamsonShmoys.HasPlanarDrawingOn B) :
    WilliamsonShmoys.HasPlanarDrawingOn A := by sorry
