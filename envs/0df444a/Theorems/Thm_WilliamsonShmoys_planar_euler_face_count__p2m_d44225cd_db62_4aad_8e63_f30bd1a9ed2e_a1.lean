-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
-- name    : WilliamsonShmoys.planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:23:15.232906+00:00
-- url     : https://prove2.me/theorems/990e11e7-778c-42e5-bda1-59c63a56dc20
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   Every finite connected graph with a drawing satisfying HasPlanarDrawingOn has a natural-number face count satisfying Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_euler_face_count__p2m_d44225cd_db62_4aad_8e63_f30bd1a9ed2e_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hconn : K.Connected) : Exists fun f : Nat => Fintype.card V + f = K.edgeSet.ncard + 2 := by sorry
