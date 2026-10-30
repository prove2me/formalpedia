-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:41:15.644526+00:00
-- url     : https://prove2.me/theorems/579647e6-6943-4df2-b38b-836f1e96da3c
-- title:
--   Euler face-count witness for a maximal planar drawing
-- statement:
--   For a drawable inclusion maximal simple graph on at least three vertices, there is a natural number f such that n + f = m + 2 and 2m ≤ 3f, where n is the number of vertices and m the number of edges. The witness represents the number of faces in a spherical embedding: Euler’s relation gives the equality, and triangular faces give the inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_aad1f7a7_a04a_47ce_bdaf_91f7c06a5480_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M) :
    ∃ f : ℕ, Fintype.card V + f = M.edgeSet.ncard + 2 ∧
      2 * M.edgeSet.ncard ≤ 3 * f := by sorry
