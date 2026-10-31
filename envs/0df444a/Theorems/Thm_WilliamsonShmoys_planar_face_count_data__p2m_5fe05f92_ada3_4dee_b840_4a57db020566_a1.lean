-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1
-- name    : WilliamsonShmoys.planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:35:32.253104+00:00
-- url     : https://prove2.me/theorems/8494d434-ba1f-46ca-922b-9ced4cfa5b5b
-- title:
--   Euler and face-count inequalities for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and the supplied planar drawing, there is a number of faces f such that every face contributes at least three boundary-edge occurrences in total, while every edge is counted twice, and Euler’s formula holds: 3f ≤ 2E and V + f = E + 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_face_count_data__p2m_5fe05f92_ada3_4dee_b840_4a57db020566_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconnected : H.Connected)
    (hV : 3 <= Fintype.card V) :
    ∃ f : Nat,
      3 * f <= 2 * H.edgeSet.ncard ∧
      Fintype.card V + f = H.edgeSet.ncard + 2 := by sorry
