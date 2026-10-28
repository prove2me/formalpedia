-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1
-- name    : WilliamsonShmoys.exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:33:03.065651+00:00
-- url     : https://prove2.me/theorems/2c89007e-1615-4d05-9613-487af383d638
-- title:
--   Finite edge-count maximization among supergraphs
-- statement:
--   For a finite vertex type, any predicate on simple graphs that holds of J admits a supergraph of J satisfying that predicate whose edge count is at least that of every further supergraph satisfying the predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_max_edge_count_supergraph__p2m_eef664be_1603_4195_b44b_d81e1ccffc6c_a1
    {V : Type} [Fintype V]
    (J : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hJ : P J) :
    ∃ K : SimpleGraph V, J ≤ K ∧ P K ∧
      ∀ L : SimpleGraph V, K ≤ L → P L →
        L.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry
