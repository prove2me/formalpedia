-- Prove2me | Theorems.Thm_WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- name    : WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:43:19.353596+00:00
-- url     : https://prove2.me/theorems/ef98b332-7c2b-49ae-9493-b96e0ba5239c
-- title:
--   Euler and face counts imply the planar edge bound
-- statement:
--   If a finite graph with at least three vertices has a natural-number face count satisfying Euler’s equation and the face-boundary inequality, then its edge count is at most three times its vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys_face_data_implies_edge_bound__p2m_c59fe07e_0bca_4d4e_9b09_8335007f2f58_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdata : ∃ f : ℕ,
      (Fintype.card V : ℤ) - (K.edgeSet.ncard : ℤ) + (f : ℤ) = 2 ∧
      (3 : ℤ) * (f : ℤ) ≤ 2 * (K.edgeSet.ncard : ℤ)) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
