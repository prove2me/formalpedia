-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_certificate_edge_bound
-- name    : WilliamsonShmoys.planar_face_certificate_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T23:09:01.202919+00:00
-- url     : https://prove2.me/theorems/04826b4b-fefa-45a5-9086-39ac41d8854b
-- title:
--   Face-counting data imply the planar edge bound
-- statement:
--   Euler’s relation, total boundary length twice the edge count, and a minimum length of three for each face imply the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_certificate_edge_bound
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (faceCount : ℕ)
    (boundaryLength : Fin faceCount → ℕ)
    (hEuler : Fintype.card V + faceCount = K.edgeSet.ncard + 2)
    (hIncidence : (∑ i : Fin faceCount, boundaryLength i) = 2 * K.edgeSet.ncard)
    (hBoundary : ∀ i : Fin faceCount, 3 ≤ boundaryLength i) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
