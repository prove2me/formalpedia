-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- name    : WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:52:55.718423+00:00
-- url     : https://prove2.me/theorems/3a65eae3-5ff7-4fce-93d5-4a7db05ee858
-- title:
--   Triangular face incidence in a maximal planar graph
-- statement:
--   Given the Euler face count for this connected drawing, maximality implies every face is triangular, so twice the edge count equals three times the face count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_maximal_planar_triangular_face_incidence__p2m_a5abbcfc_8844_40a4_806c_eef213b4f62c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hHplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (f : ℕ)
    (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2) :
    2 * H.edgeSet.ncard = 3 * f := by sorry
