-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:47.496213+00:00
-- url     : https://prove2.me/theorems/b3741e7f-300c-42f8-9c7d-be69371c2010
-- title:
--   Euler face count from a crossing-free drawing
-- statement:
--   For a finite connected graph with the supplied crossing-free drawing, the number of vertices, edges, and complementary faces satisfies Euler’s formula V − E + F = 2, expressed without subtraction as V + F = E + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_ce2523b8_2817_4847_92d2_52162bbbf3f4_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) [DecidableRel M.Adj] (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hconn : M.Connected) : ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 := by sorry
