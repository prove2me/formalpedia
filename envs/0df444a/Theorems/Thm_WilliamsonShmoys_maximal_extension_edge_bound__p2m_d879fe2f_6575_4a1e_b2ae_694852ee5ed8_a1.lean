-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- name    : WilliamsonShmoys.maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T10:13:29.644842+00:00
-- url     : https://prove2.me/theorems/7a383fbb-0fd7-48f2-a008-d521441e8559
-- title:
--   Edge bound transfers across graph equality
-- statement:
--   If two finite simple graphs contain one another and one has the triangulation edge count, then the other satisfies the corresponding edge-count lower bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1 {V : Type} [Fintype V] [LinearOrder V] (M N : SimpleGraph V) (hMN : M ≤ N) (hNM : N ≤ M) (hN : N.edgeSet.ncard + 6 = 3 * Fintype.card V) : 3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by sorry
