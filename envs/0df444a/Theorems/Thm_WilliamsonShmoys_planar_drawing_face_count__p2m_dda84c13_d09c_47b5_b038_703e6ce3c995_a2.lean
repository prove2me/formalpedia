-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2
-- name    : WilliamsonShmoys.planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:08:54.255976+00:00
-- url     : https://prove2.me/theorems/d44225cd-db62-4aad-8e63-f30bd1a9ed2e
-- title:
--   Euler face count and face-boundary estimate for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn, there is a natural number f of faces such that |V| + f = |E| + 2 and 3f <= 2|E|.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_face_count__p2m_dda84c13_d09c_47b5_b038_703e6ce3c995_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 <= Fintype.card V) :
    Exists fun f : Nat =>
      Fintype.card V + f = K.edgeSet.ncard + 2 /\
      3 * f <= 2 * K.edgeSet.ncard := by
  sorry
