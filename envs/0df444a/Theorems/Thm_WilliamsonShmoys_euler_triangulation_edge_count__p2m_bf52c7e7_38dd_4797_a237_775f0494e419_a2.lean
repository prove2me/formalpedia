-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- name    : WilliamsonShmoys.euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:36:45.933338+00:00
-- url     : https://prove2.me/theorems/ab176682-e841-4a27-a7b1-fc32b6cd602d
-- title:
--   Edge count from Euler and triangular face counts
-- statement:
--   Natural-number vertex, edge, and face counts satisfying Euler’s equation and the triangular face-incidence equation satisfy the claimed edge-count identity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

set_option autoImplicit false

theorem WilliamsonShmoys.euler_triangulation_edge_count__p2m_bf52c7e7_38dd_4797_a237_775f0494e419_a2 (v e f : Nat) (hEuler : v + f = e + 2) (hTri : 3 * f = 2 * e) : 3 * v = e + 6 := by sorry
