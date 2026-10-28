-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_certificate_of_edge_bounds
-- name    : WilliamsonShmoys.face_certificate_of_edge_bounds
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T09:36:07.232677+00:00
-- url     : https://prove2.me/theorems/e0004c66-cadb-4ce6-8976-2f14c3a2af8a
-- title:
--   Construct a numerical face certificate from edge bounds
-- statement:
--   The lower and upper edge-count bounds, together with at least three vertices, suffice to construct a natural number of formal faces and integer degrees satisfying the target equations and minimum-degree condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_certificate_of_edge_bounds
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hLower : Fintype.card V <= K.edgeSet.ncard + 1)
    (hUpper : K.edgeSet.ncard + 6 <= 3 * Fintype.card V) :
    ∃ (m : Nat) (degree : Fin m → ℤ),
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + m = 2 ∧
      (∑ f : Fin m, degree f) = 2 * (K.edgeSet.ncard : ℤ) ∧
      (∀ f, 3 <= degree f) := by sorry
