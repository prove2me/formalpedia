-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:17:37.248984+00:00
-- url     : https://prove2.me/theorems/8980508c-eade-47a8-94c5-e0127b6a85f8
-- title:
--   Euler and face-incidence equations for a maximal planar drawing
-- statement:
--   An inclusion-maximal drawable graph on at least three vertices has a face count satisfying Euler's equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_f5f2a8b8_a8d9_45a6_8446_39002bc3ddba_a8
    {V : Type} [Fintype V] [LinearOrder V]
    (K H : SimpleGraph V)
    (hV : LE.le 3 (Fintype.card V))
    (hsub : Set.Subset K.edgeSet H.edgeSet)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ H' : SimpleGraph V,
      Set.Subset H.edgeSet H'.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn H' →
      H'.edgeSet = H.edgeSet) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  sorry
