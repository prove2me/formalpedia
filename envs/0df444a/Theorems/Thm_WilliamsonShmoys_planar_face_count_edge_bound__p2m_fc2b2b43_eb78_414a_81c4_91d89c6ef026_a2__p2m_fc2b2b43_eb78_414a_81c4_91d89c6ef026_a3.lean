-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
-- name    : WilliamsonShmoys.planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:07:37.692153+00:00
-- url     : https://prove2.me/theorems/f538bb79-9891-4bc9-ac2a-67be2a4275f5
-- title:
--   Edge bound from planar face counts
-- statement:
--   Derive the edge lower bound from the two face-count equations. For a witness `f`, multiply Euler’s equation by three and substitute the incidence equation; natural-number arithmetic gives `3 * |V| = |E| + 6`, which implies the requested inequality. This lemma is independent of the drawing and maximality hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_face_count_edge_bound__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a2__p2m_fc2b2b43_eb78_414a_81c4_91d89c6ef026_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (h : exists f : Nat, Fintype.card V + f = K.edgeSet.ncard + 2 /\ 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
