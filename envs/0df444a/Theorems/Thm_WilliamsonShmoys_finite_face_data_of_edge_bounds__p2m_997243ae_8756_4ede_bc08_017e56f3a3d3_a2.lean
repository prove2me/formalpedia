-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- name    : WilliamsonShmoys.finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T20:29:57.643475+00:00
-- url     : https://prove2.me/theorems/6e200606-c393-45c6-9b41-bb9b3b87ab36
-- title:
--   Realize finite face data from edge bounds
-- statement:
--   Given at least three vertices and edge bounds placing the edge count between the connected-graph lower bound and the simple planar upper bound, construct a finite face type and lengths satisfying the target’s Euler, incidence, and minimum-length equations. Use `m − n + 2` faces, give each length three, and assign the remaining incidence count to one face.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2

theorem WilliamsonShmoys.finite_face_data_of_edge_bounds__p2m_997243ae_8756_4ede_bc08_017e56f3a3d3_a2
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hlo : Fintype.card V ≤ K.edgeSet.ncard + 1)
    (hhi : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6) :
    Nonempty (WilliamsonShmoys.PlanarFaceData__p2m_a9372b74_2333_4a1d_b694_ab95253c7875_a2 K) := by sorry
