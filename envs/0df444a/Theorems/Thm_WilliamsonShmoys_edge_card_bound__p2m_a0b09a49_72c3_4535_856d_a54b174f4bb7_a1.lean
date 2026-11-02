-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- name    : WilliamsonShmoys.edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:38.786993+00:00
-- url     : https://prove2.me/theorems/5a480ab8-5fac-432d-937a-5637013bfdae
-- title:
--   Finite simple graphs have a uniform edge-count bound
-- statement:
--   For a finite vertex type, there is a natural-number bound on the edge count of every simple graph on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1 {V : Type} [Fintype V] : ∃ N : Nat, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card ≤ N := by sorry
