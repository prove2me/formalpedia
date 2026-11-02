-- Prove2me | Theorems.Thm_WilliamsonShmoys_supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
-- name    : WilliamsonShmoys.supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:46:53.575653+00:00
-- url     : https://prove2.me/theorems/de823218-b35b-47b7-9852-26ba1b994051
-- title:
--   Finite supergraph with an Euler-style certificate
-- statement:
--   A finite simple graph on at least three vertices with at most $3|V|-6$ edges has a supergraph and natural number satisfying the target’s edge monotonicity, equation, and inequality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.supergraph_euler_certificate_of_edge_bound__p2m_e37f737c_f285_4a30_83a0_16b070403a61_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hbound : letI : DecidableRel G.Adj := Classical.decRel G.Adj
      G.edgeFinset.card ≤ 3 * Fintype.card V - 6) :
    ∃ (H : SimpleGraph V) (f : ℕ),
      G ≤ H ∧
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card ≤ H.edgeFinset.card) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       Fintype.card V + f = H.edgeFinset.card + 2) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       3 * f ≤ 2 * H.edgeFinset.card) := by sorry
