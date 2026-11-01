-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:55.024816+00:00
-- url     : https://prove2.me/theorems/5d494874-3848-4892-940c-cf6b084398e7
-- title:
--   Euler face counts from a connected planar drawing
-- statement:
--   For a connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn, there is a natural-number face count satisfying Euler’s equation and the bound that the total face-boundary length is at least three per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_counts__p2m_376b67ec_1efe_4ea0_9e38_4777b8820599_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * H.edgeFinset.card := by sorry
