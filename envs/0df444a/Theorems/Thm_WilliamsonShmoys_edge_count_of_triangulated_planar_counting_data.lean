-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_triangulated_planar_counting_data
-- name    : WilliamsonShmoys.edge_count_of_triangulated_planar_counting_data
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:54:49.98922+00:00
-- url     : https://prove2.me/theorems/cf67d339-4435-48e3-be84-9ccfa1205df7
-- title:
--   Triangular-face counting identities determine the edge count
-- statement:
--   For a finite graph, Euler’s identity and the degree sum for triangular faces imply that the edge count plus six equals three times the vertex count. This child isolates the finite counting and arithmetic step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarCountingData
set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_of_triangulated_planar_counting_data
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (D : WilliamsonShmoys.TriangulatedPlanarCountingData K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
