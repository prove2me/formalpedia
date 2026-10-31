-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
-- name    : WilliamsonShmoys.maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:58:54.284849+00:00
-- url     : https://prove2.me/theorems/301f4675-a625-4f03-8421-053f86d64c99
-- title:
--   Euler and triangular face-count equations
-- statement:
--   A maximal drawable simple graph on at least three vertices has a natural-number face count satisfying Euler’s equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_equations__p2m_27a5cf8c_cedc_4abf_b82c_50a7768c797c_a2
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hG : HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → HasPlanarDrawingOn K → K = G) :
    ∃ f : ℕ,
      Fintype.card V + f = G.edgeSet.ncard + 2 ∧
      3 * f = 2 * G.edgeSet.ncard := by sorry
