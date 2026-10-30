-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:54:55.410363+00:00
-- url     : https://prove2.me/theorems/73871160-1692-421c-aaf6-a7b2b6384c07
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is maximal among drawable supergraphs admits a face count satisfying Euler's equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_dc9018d8_e47b_47c1_8eef_84ccb4273562_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hmax : ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U ≤ T) (hV : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = T.edgeSet.ncard + 2 ∧ 3 * f = 2 * T.edgeSet.ncard := by sorry
