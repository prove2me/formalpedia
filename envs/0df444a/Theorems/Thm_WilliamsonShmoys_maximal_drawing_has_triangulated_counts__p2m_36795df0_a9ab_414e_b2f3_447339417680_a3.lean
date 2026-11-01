-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_triangulated_counts__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
-- name    : WilliamsonShmoys.maximal_drawing_has_triangulated_counts__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:00:06.044035+00:00
-- url     : https://prove2.me/theorems/7e50d4d0-4707-47ef-8dc4-efddfbe56298
-- title:
--   Euler and face-incidence counts for a maximal planar drawing
-- statement:
--   For a maximal drawable simple graph on at least three vertices, there is a natural face count satisfying Euler’s equation and the triangular face-edge incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawing_has_triangulated_counts__p2m_36795df0_a9ab_414e_b2f3_447339417680_a3 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) (hcard : 3 ≤ Fintype.card V) : (letI : DecidableRel K.Adj := Classical.decRel K.Adj; ∃ f : ℕ, Fintype.card V + f = K.edgeFinset.card + 2 ∧ 3 * f = 2 * K.edgeFinset.card) := by sorry
