-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- name    : WilliamsonShmoys.planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:02.866281+00:00
-- url     : https://prove2.me/theorems/6cffaacd-857e-41eb-9cea-5971a976511e
-- title:
--   Facial boundary data and Euler’s equation imply the planar edge bound
-- statement:
--   Sum the face boundary lower bounds to get three times the face count at most twice the edge count. Substitute Euler’s equation and use the at-least-three-vertices hypothesis to conclude the edge bound, including the natural-number subtraction by six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_certificate_edge_bound__p2m_42c50023_969e_4d67_9641_cde1dc4669ab_a2
    {V : Type} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (faceCount : Nat)
    (hcard : 3 ≤ Fintype.card V)
    (hboundary : ∃ boundaryLength : Fin faceCount → Nat,
      (∑ f : Fin faceCount, boundaryLength f) = 2 * K.edgeFinset.card ∧
      (∀ f : Fin faceCount, 3 ≤ boundaryLength f))
    (heuler : Fintype.card V + faceCount = K.edgeFinset.card + 2) :
    K.edgeFinset.card ≤ 3 * Fintype.card V - 6 := by
  sorry
