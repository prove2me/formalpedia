-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- name    : WilliamsonShmoys.planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:05.601141+00:00
-- url     : https://prove2.me/theorems/0ea129f4-3238-4899-8c4a-237a80d1c906
-- title:
--   Euler and face data for a planar completion
-- statement:
--   For a drawable simple graph with at least three vertices, there are natural numbers m' and f such that the graph has at most m' edges, the vertex and face counts satisfy Euler’s relation, and the face-edge incidence inequality holds. A proof route is to add noncrossing edges to connect components and triangulate a maximal drawing, then count faces and edge incidences.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) : ∃ (m' f : ℕ), R.edgeSet.ncard ≤ m' ∧ Fintype.card V + f = m' + 2 ∧ 3 * f ≤ 2 * m' := by sorry
