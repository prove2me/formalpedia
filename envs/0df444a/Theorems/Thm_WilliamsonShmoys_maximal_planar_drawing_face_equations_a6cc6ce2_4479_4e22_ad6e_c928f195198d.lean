-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations_a6cc6ce2_4479_4e22_ad6e_c928f195198d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:40:54.440316+00:00
-- url     : https://prove2.me/theorems/66fe11ea-5ded-4a16-9252-19c309f901c3
-- title:
--   Euler and triangular-face equations for maximal drawings
-- statement:
--   For a drawable graph maximal among drawable supergraphs on the same finite vertex type, with at least three vertices, there is a natural-number face count f satisfying Euler's equation n + f = E + 2 and the triangular face-edge incidence equation 3f = 2E. These equations imply E + 6 = 3n. The independent proof route is to convert the arc drawing to a plane embedding, prove maximality forces connectedness and triangular faces, and count vertices, faces, and edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations_a6cc6ce2_4479_4e22_ad6e_c928f195198d
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      3 * f = 2 * M.edgeSet.ncard := by sorry
