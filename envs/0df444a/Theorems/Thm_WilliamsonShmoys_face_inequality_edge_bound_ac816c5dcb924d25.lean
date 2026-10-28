-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_inequality_edge_bound_ac816c5dcb924d25
-- name    : WilliamsonShmoys.face_inequality_edge_bound_ac816c5dcb924d25
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:12:52.123475+00:00
-- url     : https://prove2.me/theorems/2ee817de-fa96-4774-82d7-ce142a56f1e7
-- title:
--   Edge bound from Euler and face inequality
-- statement:
--   If the vertex, face, and edge counts satisfy Euler’s equation and the aggregate face-length inequality, then the simple planar edge bound follows by arithmetic.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.face_inequality_edge_bound_ac816c5dcb924d25
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (f : Nat)
    (hEuler : Fintype.card V + f = H.edgeSet.ncard + 2)
    (hFaces : 3 * f ≤ 2 * H.edgeSet.ncard) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
