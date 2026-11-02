-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- name    : WilliamsonShmoys.edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:48:59.393785+00:00
-- url     : https://prove2.me/theorems/d2c209d8-72da-4c67-bb7c-c30661005ca8
-- title:
--   Edge cardinality is invariant under mutual inclusion
-- statement:
--   Two finite simple graphs on the same vertex type with mutual adjacency inclusion have equal edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M K : SimpleGraph V) (hMK : M ≤ K) (hKM : K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     M.edgeFinset.card = K.edgeFinset.card) := by sorry
