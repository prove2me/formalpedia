-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count
-- name    : WilliamsonShmoys.euler_face_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T20:25:20.701977+00:00
-- url     : https://prove2.me/theorems/65f7307a-7178-49b6-ad7d-c45bd26ca1b0
-- title:
--   Euler face count for a connected drawn graph
-- statement:
--   A finite connected graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has a finite face count obeying Euler’s equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
