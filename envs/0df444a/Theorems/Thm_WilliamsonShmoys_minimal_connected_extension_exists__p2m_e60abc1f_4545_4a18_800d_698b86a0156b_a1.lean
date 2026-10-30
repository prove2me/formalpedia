-- Prove2me | Theorems.Thm_WilliamsonShmoys_minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- name    : WilliamsonShmoys.minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:10.959751+00:00
-- url     : https://prove2.me/theorems/5386f246-6d63-4306-885f-dbaa8083f5e2
-- title:
--   Existence of an inclusion-minimal connected supergraph
-- statement:
--   Among connected supergraphs of M, there is one that has no strictly smaller connected subgraph still containing M. The proof route is to minimize the finite number of edges among connected supergraphs; the complete graph supplies a candidate. Finiteness and nonemptiness are retained, including the singleton case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false
open SimpleGraph

theorem WilliamsonShmoys.minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
    {V : Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → H ≤ K := by sorry
