-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_faces__p2m_6360b5b8_545a_4187_945d_5d0aa3896a85_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_faces__p2m_6360b5b8_545a_4187_945d_5d0aa3896a85_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:02:21.076617+00:00
-- url     : https://prove2.me/theorems/dab5f445-9f6e-43eb-b546-caa307c8ab83
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, there is a natural number of faces satisfying Euler’s vertex-edge-face relation. This isolates the topological face-counting work; the parent chooses the directed edge-incidence count as twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_faces__p2m_6360b5b8_545a_4187_945d_5d0aa3896a85_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (dK : DecidableRel K.Adj) (hconn : K.Connected) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ f : Nat, Fintype.card V + f = K.edgeFinset.card + 2 := by sorry
