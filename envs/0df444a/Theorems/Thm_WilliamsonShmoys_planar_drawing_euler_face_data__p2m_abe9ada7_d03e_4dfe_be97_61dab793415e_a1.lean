-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T08:23:51.08435+00:00
-- url     : https://prove2.me/theorems/dbab630e-c01d-4b47-9ab6-dd56c8211fc8
-- title:
--   Euler and face-boundary counts for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has a natural-number face count satisfying Euler’s equation and the lower bound of three edge sides per face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_data__p2m_abe9ada7_d03e_4dfe_be97_61dab793415e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hConn : K.Connected)
    (hK : HasPlanarDrawingOn K)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f ≤ 2 * K.edgeSet.ncard := by sorry
