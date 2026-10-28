-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_certificate_edge_bound
-- name    : WilliamsonShmoys.face_certificate_edge_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:18:49.947831+00:00
-- url     : https://prove2.me/theorems/be6011c8-166a-4527-9c87-0ad1b13bda66
-- title:
--   Euler face data implies the planar edge bound
-- statement:
--   For a finite simple graph with at least three vertices, Euler’s equation, total face degree twice the edge count, and face degrees at least three imply the planar edge bound. Sum the face-degree inequalities to obtain `3m ≤ 2E`, combine with Euler’s equation, and convert the resulting integer inequality to naturals.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_certificate_edge_bound
    {V : Type} [Fintype V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (m : Nat) (degree : Fin m → ℤ)
    (heuler : (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + m = 2)
    (hincidence : (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : ℤ))
    (hdegree : ∀ f, 3 ≤ degree f) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
