-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_aux
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition_aux
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T10:07:20.774306+00:00
-- url     : https://prove2.me/theorems/9f8bc1ea-7986-4193-ad7f-60ca989b68d3
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For an inclusion-maximal planar drawing on at least three vertices, there is a number of faces satisfying Euler’s equation and the triangular face-edge incidence equation. These equations imply the edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition_aux
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by sorry
