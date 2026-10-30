-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1
-- name    : WilliamsonShmoys.maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:48.628226+00:00
-- url     : https://prove2.me/theorems/506eecf6-5eda-45c5-8776-41c7d7d68a5c
-- title:
--   Euler and triangular-face equations for a maximal planar drawing
-- statement:
--   A finite crossing-free drawing on at least three vertices that is maximal among drawable supergraphs has a face count satisfying Euler’s equation and the triangular face-edge incidence equation. These yield the exact edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_decomposition__p2m_7a0d3f25_089a_4d82_a9d5_85ef68cd5f10_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) (hMax : ∀ N : SimpleGraph V, L ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N = L) (hCard : 3 ≤ Fintype.card V) : ∃ f : ℕ, Fintype.card V + f = L.edgeSet.ncard + 2 ∧ 3 * f = 2 * L.edgeSet.ncard := by sorry
