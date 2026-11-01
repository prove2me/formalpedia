-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:39:12.810433+00:00
-- url     : https://prove2.me/theorems/5de819de-a434-4eee-9d51-0646a941be0a
-- title:
--   Euler and face incidence equations for a maximal planar drawing
-- statement:
--   For a drawable simple graph on at least three vertices that is maximal among drawable supergraphs on the same vertex set, there is a natural number f, the number of faces, satisfying Euler’s equation |V| + f = |E| + 2 and the triangular face-edge incidence equation 3f = 2|E|. The three-vertex case is included; its embedding has two triangular faces. The first equation formalizes Euler’s characteristic for the plane map extracted from the drawing. The second follows by showing that maximality forces every face boundary to be a triangle. A proof route is to derive cyclic orders at vertices from the arcs, construct the facial boundary walks, prove Euler’s formula for the resulting finite plane map, and use maximality to exclude any face boundary with more than three edges. Together these equations reduce the target to arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_face_incidence__p2m_4ca6b67e_a5cb_47ee_9958_b87be2ab6440_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K →
      H.edgeFinset ⊆ K.edgeFinset →
      K.edgeFinset ⊆ H.edgeFinset) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeFinset.card + 2 ∧
      3 * f = 2 * H.edgeFinset.card := by sorry
