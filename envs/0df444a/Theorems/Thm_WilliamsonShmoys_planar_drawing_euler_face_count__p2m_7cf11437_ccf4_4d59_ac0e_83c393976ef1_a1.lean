-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:15:24.813452+00:00
-- url     : https://prove2.me/theorems/455fa535-cdaa-49e5-9b93-fdaf971c0b4d
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   A connected graph with at least three vertices and the supplied crossing-free drawing has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_7cf11437_ccf4_4d59_ac0e_83c393976ef1_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : ∃ f : ℕ, Fintype.card V + f = T.edgeSet.ncard + 2 := by sorry
