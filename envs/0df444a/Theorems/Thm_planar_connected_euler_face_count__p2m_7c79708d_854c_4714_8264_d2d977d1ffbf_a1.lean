-- Prove2me | Theorems.Thm_planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- name    : planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:34:58.953721+00:00
-- url     : https://prove2.me/theorems/422010ac-e404-45c7-bd98-f3385e323913
-- title:
--   Euler face count for a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn, the number of complementary regions is finite and satisfies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem planar_connected_euler_face_count__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 := by
  sorry
