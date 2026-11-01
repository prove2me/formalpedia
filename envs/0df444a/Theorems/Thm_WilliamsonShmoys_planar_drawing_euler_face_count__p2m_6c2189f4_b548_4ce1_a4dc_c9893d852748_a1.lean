-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1
-- name    : WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:25:17.859985+00:00
-- url     : https://prove2.me/theorems/cc84765a-dec5-432d-9369-d01ebc3be70d
-- title:
--   Euler face count from a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free drawing, there is a natural number of faces satisfying Euler’s equation and the face-incidence lower bound. The first equality is the spherical Euler relation rearranged; the inequality follows by counting edge sides in face boundary walks, accounting for bridges appearing twice.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_euler_face_count__p2m_6c2189f4_b548_4ce1_a4dc_c9893d852748_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hconn : M.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeFinset.card + 2 ∧
      3 * f ≤ 2 * M.edgeFinset.card := by sorry
