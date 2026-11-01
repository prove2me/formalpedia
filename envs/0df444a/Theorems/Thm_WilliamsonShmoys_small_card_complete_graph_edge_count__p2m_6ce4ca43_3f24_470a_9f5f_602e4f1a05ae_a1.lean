-- Prove2me | Theorems.Thm_WilliamsonShmoys_small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- name    : WilliamsonShmoys.small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:09.904816+00:00
-- url     : https://prove2.me/theorems/bf18f02b-3f0a-45a9-b516-1c33a4cb5c55
-- title:
--   Edge count of a small complete graph
-- statement:
--   For a finite linearly ordered vertex type with fewer than three elements, the complete graph's edge finset has cardinality equal to the binomial coefficient of the vertex count and 2.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.small_card_complete_graph_edge_count__p2m_6ce4ca43_3f24_470a_9f5f_602e4f1a05ae_a1
    {V : Type} [Fintype V] [LinearOrder V]
    [DecidableRel (⊤ : SimpleGraph V).Adj]
    (hsmall : Fintype.card V < 3) :
    (⊤ : SimpleGraph V).edgeFinset.card = (Fintype.card V).choose 2 := by
  sorry
