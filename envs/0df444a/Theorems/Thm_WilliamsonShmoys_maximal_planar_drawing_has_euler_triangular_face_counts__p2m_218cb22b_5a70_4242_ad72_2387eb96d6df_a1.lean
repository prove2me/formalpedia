-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:40:43.998654+00:00
-- url     : https://prove2.me/theorems/15d9d9e3-06da-4cda-a49a-4bfa4d6bbf59
-- title:
--   Face counts for a maximal planar drawing
-- statement:
--   A maximal drawable simple graph on at least three vertices has a finite face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_has_euler_triangular_face_counts__p2m_218cb22b_5a70_4242_ad72_2387eb96d6df_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : forall M : SimpleGraph V, L <= M ->
      WilliamsonShmoys.HasPlanarDrawingOn M -> M = L)
    (hCard : 3 <= Fintype.card V) :
    ∃ f : ℕ, f + Fintype.card V = L.edgeSet.ncard + 2 ∧
      3 * f = 2 * L.edgeSet.ncard := by sorry
