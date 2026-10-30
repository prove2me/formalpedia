-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:47:34.695993+00:00
-- url     : https://prove2.me/theorems/e307fd83-c86f-42f7-8879-0524310903cd
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on those vertices, there is a face count satisfying Euler’s equation and the triangular-face edge-incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_equations__p2m_a751ad37_41e6_4dc6_8ec5_fa27c83e40b5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ K : SimpleGraph V,
      G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f = 2 * G.edgeSet.ncard := by sorry
