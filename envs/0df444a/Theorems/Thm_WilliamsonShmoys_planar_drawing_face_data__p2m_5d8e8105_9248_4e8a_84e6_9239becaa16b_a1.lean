-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- name    : WilliamsonShmoys.planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:01:09.983792+00:00
-- url     : https://prove2.me/theorems/1d9982e7-ae2e-41b5-99c8-f768b7d6d77d
-- title:
--   Euler and boundary data from a planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there are a face count F and total boundary length B satisfying Euler’s relation, a lower bound of three per face, and the fact that each edge contributes twice to the total boundary length. The size hypothesis is needed to rule out facial boundary walks of length one or two; bridges still contribute twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_data__p2m_5d8e8105_9248_4e8a_84e6_9239becaa16b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ F B : ℕ,
      Fintype.card V + F = K.edgeFinset.card + 2 ∧
      3 * F ≤ B ∧
      B = 2 * K.edgeFinset.card := by sorry
