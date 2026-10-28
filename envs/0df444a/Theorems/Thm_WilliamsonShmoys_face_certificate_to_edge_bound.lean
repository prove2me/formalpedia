-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_certificate_to_edge_bound
-- name    : WilliamsonShmoys.face_certificate_to_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:39:45.741724+00:00
-- url     : https://prove2.me/theorems/ca44351c-17c9-45cc-a207-1c39d427abf1
-- title:
--   Euler edge bound from a finite face certificate
-- statement:
--   If a finite positive collection of faces satisfies Euler’s relation, has total boundary length twice the edge count, and every boundary has length at least three, then the edge count is at most three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem WilliamsonShmoys.face_certificate_to_edge_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (F : ℕ)
    (faceLength : Fin F → ℕ)
    (hF : 0 < F)
    (hEuler : Fintype.card V + F = L.edgeSet.ncard + 2)
    (hIncidences : (∑ i : Fin F, faceLength i) = 2 * L.edgeSet.ncard)
    (hFaceLength : ∀ i, 3 ≤ faceLength i)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  sorry
