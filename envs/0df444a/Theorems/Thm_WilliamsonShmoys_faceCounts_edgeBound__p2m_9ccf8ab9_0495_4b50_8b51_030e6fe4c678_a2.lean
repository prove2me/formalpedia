-- Prove2me | Theorems.Thm_WilliamsonShmoys_faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
-- name    : WilliamsonShmoys.faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:18:15.177467+00:00
-- url     : https://prove2.me/theorems/faa65594-066f-4505-8c15-1e4a967bb499
-- title:
--   Derive the edge bound from face counts
-- statement:
--   Given the Euler equation, the incidence sum, face lengths of at least three, and at least three vertices, the edge bound follows by summing the face-length inequalities to obtain 3F ≤ 2E and combining that with Euler’s equation. This isolates the arithmetic from the parent. A direct proof route is finite-sum monotonicity followed by casting the resulting inequalities to integers and arithmetic normalization.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.faceCounts_edgeBound__p2m_9ccf8ab9_0495_4b50_8b51_030e6fe4c678_a2 {V : Type} [Fintype V] (H : SimpleGraph V) (F : ℕ) (faceLength : Fin F → ℕ) (hEuler : (Fintype.card V : ℤ) - (H.edgeSet.ncard : ℤ) + (F : ℤ) = 2) (hIncidences : (∑ f : Fin F, faceLength f) = 2 * H.edgeSet.ncard) (hFaceLength : ∀ f, 3 ≤ faceLength f) (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
