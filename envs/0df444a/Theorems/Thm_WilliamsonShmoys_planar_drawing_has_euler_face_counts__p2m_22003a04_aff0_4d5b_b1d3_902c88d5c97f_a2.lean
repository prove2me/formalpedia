-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
-- name    : WilliamsonShmoys.planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:32.791895+00:00
-- url     : https://prove2.me/theorems/2fa1cccf-2cb6-486c-a6c5-c4c514b22b8e
-- title:
--   Extract Euler edge and face counts from a planar drawing
-- statement:
--   Construct edge and face counts for the finite connected graph’s given crossing-free drawing. Euler’s equation relates the vertex, face, and edge counts; counting edge-face incidences gives the lower bound of three incidences per face. The hypotheses retain the size and connectedness conditions needed by that face-boundary argument. A proof route is to turn the arc drawing into a plane embedding, apply Euler’s formula, then count boundary incidences, counting repeated bridge incidences in the face walks.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_has_euler_face_counts__p2m_22003a04_aff0_4d5b_b1d3_902c88d5c97f_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ edgeCount faceCount : ℕ,
      G.edgeSet.ncard = edgeCount ∧
      Fintype.card V + faceCount = edgeCount + 2 ∧
      3 * faceCount <= 2 * edgeCount := by sorry
