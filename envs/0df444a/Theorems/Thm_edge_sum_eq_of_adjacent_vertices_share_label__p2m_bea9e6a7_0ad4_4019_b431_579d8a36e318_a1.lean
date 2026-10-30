-- Prove2me | Theorems.Thm_edge_sum_eq_of_adjacent_vertices_share_label__p2m_bea9e6a7_0ad4_4019_b431_579d8a36e318_a1
-- name    : edge_sum_eq_of_adjacent_vertices_share_label__p2m_bea9e6a7_0ad4_4019_b431_579d8a36e318_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:54:15.327819+00:00
-- url     : https://prove2.me/theorems/3439e91d-67a7-4996-874d-b3698a3b025c
-- title:
--   Edge counts across label fibers
-- statement:
--   For a finite graph whose adjacent vertices always have the same label, the sum of the edge counts of the graphs induced on each label fiber equals the graph's edge count. The fibers partition vertices, and the adjacency hypothesis ensures every edge lies in exactly one fiber.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem edge_sum_eq_of_adjacent_vertices_share_label__p2m_bea9e6a7_0ad4_4019_b431_579d8a36e318_a1 {V ι : Type} [Fintype V] [Fintype ι] (G : SimpleGraph V) (label : V → ι) (h : ∀ ⦃u v : V⦄, G.Adj u v → label u = label v) : (Finset.univ.sum fun i : ι => (G.induce {v : V | label v = i}).edgeSet.ncard) = G.edgeSet.ncard := by sorry
