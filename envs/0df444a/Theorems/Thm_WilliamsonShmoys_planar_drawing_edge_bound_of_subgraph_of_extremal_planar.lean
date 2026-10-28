-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_of_subgraph_of_extremal_planar
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_of_subgraph_of_extremal_planar
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T18:21:23.513088+00:00
-- url     : https://prove2.me/theorems/db5fb187-cf2f-4319-b3fe-a1a4d673ae08
-- title:
--   Edge bound from a subgraph of an extremal graph
-- statement:
--   If a finite simple graph is a subgraph of a graph whose edge count is 3|V| − 6, then its edge count is at most 3|V| − 6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound_of_subgraph_of_extremal_planar {V : Type} [Fintype V] [LinearOrder V] (G H : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hGH : G ≤ H) (hHE : H.edgeSet.ncard + 6 = 3 * Fintype.card V) : G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
