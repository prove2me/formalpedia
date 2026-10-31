-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:56:50.161737+00:00
-- url     : https://prove2.me/theorems/e4b756e2-e047-4436-8932-b1de6946862d
-- title:
--   Face count equations for a maximal planar drawing
-- statement:
--   Produce a natural number of faces satisfying Euler’s equation and the triangular face-edge incidence equation for a maximal drawing. The Euler equation requires the maximal plane graph to be connected; the incidence equation requires every face to be triangular. A proof route is to establish connectivity, use Euler’s formula, then show a face with more than three boundary sides permits adding a drawable edge. At exactly three vertices, the equations hold for the triangular embedding.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_count_certificate__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ H : SimpleGraph V, K ≤ H → WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ K) :
    ∃ f : ℕ, Fintype.card V + f = K.edgeSet.ncard + 2 ∧ 3 * f = 2 * K.edgeSet.ncard := by sorry
