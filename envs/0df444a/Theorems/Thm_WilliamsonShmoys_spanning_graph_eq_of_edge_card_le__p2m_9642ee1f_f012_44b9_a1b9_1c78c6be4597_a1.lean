-- Prove2me | Theorems.Thm_WilliamsonShmoys_spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- name    : WilliamsonShmoys.spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:08:00.809623+00:00
-- url     : https://prove2.me/theorems/c22e0933-7566-41e4-a566-7b9894f0a381
-- title:
--   Equal-sized spanning simple graphs are equal
-- statement:
--   If one finite simple graph contains every edge of another and has no more edges, then the two graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.spanning_graph_eq_of_edge_card_le__p2m_9642ee1f_f012_44b9_a1b9_1c78c6be4597_a1 {V : Type} [Fintype V] (G K : SimpleGraph V) (hGK : ∀ ⦃u v : V⦄, G.Adj u v → K.Adj u v) (hcard : (letI : DecidableRel G.Adj := Classical.decRel G.Adj; letI : DecidableRel K.Adj := Classical.decRel K.Adj; K.edgeFinset.card ≤ G.edgeFinset.card)) : K = G := by sorry
