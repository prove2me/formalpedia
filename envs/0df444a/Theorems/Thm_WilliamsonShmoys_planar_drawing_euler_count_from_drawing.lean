-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_count_from_drawing
-- name    : WilliamsonShmoys.planar_drawing_euler_count_from_drawing
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T15:16:51.286259+00:00
-- url     : https://prove2.me/theorems/8af12bbd-4911-4959-b9e6-4607508a76aa
-- title:
--   Euler count from a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural number of faces satisfying the connected Euler count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_count_from_drawing {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hdraw : HasPlanarDrawingOn G) (hconn : G.Connected) : ∃ f : ℕ, Fintype.card V + f = G.edgeSet.ncard + 2 := by sorry
