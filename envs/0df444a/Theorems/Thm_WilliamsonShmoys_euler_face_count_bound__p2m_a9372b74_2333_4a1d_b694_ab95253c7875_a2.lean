-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- name    : WilliamsonShmoys.euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:52:19.038288+00:00
-- url     : https://prove2.me/theorems/23ab5a5f-868c-493f-be69-606b32a166fb
-- title:
--   Euler face data implies the planar edge bound
-- statement:
--   From finite face data asserting Euler's formula, total boundary incidence twice the edge count, and boundary length at least three for every face, derive the edge bound. The vertex lower bound is preserved from the parent theorem.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.euler_face_count_bound__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (D : WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
