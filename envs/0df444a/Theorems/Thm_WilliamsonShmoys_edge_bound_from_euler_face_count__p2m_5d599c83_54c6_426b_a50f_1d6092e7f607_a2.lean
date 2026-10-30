-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- name    : WilliamsonShmoys.edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T01:02:48.546746+00:00
-- url     : https://prove2.me/theorems/1afe5140-009a-43ba-a59a-010813f4d75c
-- title:
--   Planar edge bound from Euler face counts
-- statement:
--   The Euler face-count equation and the lower bound of three on each face boundary imply the standard planar edge bound for at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_from_euler_face_count__p2m_5d599c83_54c6_426b_a50f_1d6092e7f607_a2 {V : Type} [Fintype V] (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hData : ∃ f : Nat, Fintype.card V + f = H.edgeSet.ncard + 2 ∧ 3 * f ≤ 2 * H.edgeSet.ncard) : H.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
