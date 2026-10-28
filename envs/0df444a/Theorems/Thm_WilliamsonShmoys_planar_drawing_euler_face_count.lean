-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:46:27.577665+00:00
-- url     : https://prove2.me/theorems/bc69c174-abfe-4163-bf97-b2c9db87f3c2
-- title:
--   Euler face count from a planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula. This separates the face-count obligation from the target inequality; prove it by constructing the plane embedding and establishing Euler’s formula for that embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ f : Nat,
      (Fintype.card V : Int) - (H.edgeSet.ncard : Int) + (f : Int) = 2 := by sorry
