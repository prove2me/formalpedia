-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_bound_of_spanning_triangulation_20261026
-- name    : WilliamsonShmoys.edge_bound_of_spanning_triangulation_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:14:49.946331+00:00
-- url     : https://prove2.me/theorems/3f092e8f-29f7-4390-b367-01515caf4642
-- title:
--   Edge bound from a spanning triangulation
-- statement:
--   If a simple graph on a finite vertex type is a subgraph of another graph whose edge count is 3|V|−6, then its edge count is at most 3|V|−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_bound_of_spanning_triangulation_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (H : SimpleGraph V)
    (hsub : ∀ ⦃u v : V⦄, K.Adj u v → H.Adj u v)
    (hcard : H.edgeSet.ncard = 3 * Fintype.card V - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry
