-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:03.891276+00:00
-- url     : https://prove2.me/theorems/854ca7f2-4a2f-40b5-a832-4330138988cf
-- title:
--   Euler equation for a connected planar drawing
-- statement:
--   A finite connected graph with the supplied crossing-free drawing has a natural-number face count satisfying Euler’s equation. The child isolates the topological Euler step. A proof route is to turn the continuous drawing into a finite plane embedding, then apply Euler’s formula for connected plane graphs. The hypotheses are retained as in the parent; the lower bound on the vertex count is not needed for Euler’s formula itself.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_equation_from_planar_drawing__p2m_2fa1cccf_2cb6_486c_a6c5_c4c514b22b8e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ faceCount : ℕ,
      Fintype.card V + faceCount = G.edgeSet.ncard + 2 := by sorry
