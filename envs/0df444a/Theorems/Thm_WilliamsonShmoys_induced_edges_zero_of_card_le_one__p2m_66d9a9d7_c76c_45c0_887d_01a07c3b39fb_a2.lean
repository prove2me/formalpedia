-- Prove2me | Theorems.Thm_WilliamsonShmoys_induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2
-- name    : WilliamsonShmoys.induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:14:24.05965+00:00
-- url     : https://prove2.me/theorems/97cda368-2086-4dfc-b1c0-2d4195b72ea5
-- title:
--   An induced graph on at most one vertex has no edges
-- statement:
--   A simple graph induced on a vertex set of cardinality at most one has no edges. The child captures the graph fact needed for the singleton and empty cardinality cases; its proof route is to use that each edge has two distinct endpoints in the induced vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.induced_edges_zero_of_card_le_one__p2m_66d9a9d7_c76c_45c0_887d_01a07c3b39fb_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (s : Finset V) (hs : Fintype.card s ≤ 1) : (letI : DecidableRel (K.induce (↑s : Set V)).Adj := Classical.decRel _; (K.induce (↑s : Set V)).edgeFinset.card = 0) := by sorry
