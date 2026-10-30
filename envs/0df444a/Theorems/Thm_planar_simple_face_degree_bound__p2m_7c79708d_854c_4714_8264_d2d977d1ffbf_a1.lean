-- Prove2me | Theorems.Thm_planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- name    : planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:03.457511+00:00
-- url     : https://prove2.me/theorems/5ec8fcdd-ba42-4764-bfb5-c1bd9285046d
-- title:
--   Face-degree bound from a planar drawing and Euler count
-- statement:
--   For a finite connected simple graph with at least three vertices, any face count satisfying Euler’s equation for a crossing-free drawing obeys the total face-degree lower bound, equivalently three times the face count is at most twice the edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem planar_simple_face_degree_bound__p2m_7c79708d_854c_4714_8264_d2d977d1ffbf_a1 {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hHconn : H.Connected) (hHplanar : HasPlanarDrawingOn H)
    (f : ℕ) (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    3 * f ≤ 2 * H.edgeSet.ncard := by
  sorry
