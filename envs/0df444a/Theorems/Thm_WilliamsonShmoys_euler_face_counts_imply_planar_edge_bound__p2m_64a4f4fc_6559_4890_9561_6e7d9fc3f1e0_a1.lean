-- Prove2me | Theorems.Thm_WilliamsonShmoys_euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- name    : WilliamsonShmoys.euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:58:31.943176+00:00
-- url     : https://prove2.me/theorems/c9c0f407-913b-4a9d-b77a-703e0faa6dd6
-- title:
--   Euler and triangular-face counts imply the planar edge bound
-- statement:
--   For a finite simple graph, if its vertex, edge, and face counts satisfy Euler’s equation and the triangular face-edge incidence equation, then its edge count satisfies the requested lower bound. This is a reusable counting lemma; the equations actually imply equality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.euler_face_counts_imply_planar_edge_bound__p2m_64a4f4fc_6559_4890_9561_6e7d9fc3f1e0_a1
    {V : Type} [Fintype V]
    (K : SimpleGraph V)
    (f : ℕ)
    (hEuler : Fintype.card V + f = K.edgeSet.ncard + 2)
    (hFaces : 3 * f = 2 * K.edgeSet.ncard) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by
  sorry
