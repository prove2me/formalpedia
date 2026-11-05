-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_vertex_pair_list__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- name    : WilliamsonShmoys.finite_vertex_pair_list__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T03:17:45.910815+00:00
-- url     : https://prove2.me/theorems/c8ceede8-44b1-4bbf-ae4c-115baabb5537
-- title:
--   A finite list covers all ordered vertex pairs
-- statement:
--   For a finite type, there is a finite list containing every ordered pair of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.finite_vertex_pair_list__p2m_1f4c177d_eb20_4750_9a13_0c928226c3d6_a1
    {V : Type} [Fintype V] :
    ∃ pairs : List (V × V), ∀ u v : V, (u, v) ∈ pairs := by sorry
