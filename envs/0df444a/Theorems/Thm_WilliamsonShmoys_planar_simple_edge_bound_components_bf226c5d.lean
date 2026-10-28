-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_edge_bound_components_bf226c5d
-- name    : WilliamsonShmoys.planar_simple_edge_bound_components_bf226c5d
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:38:41.154777+00:00
-- url     : https://prove2.me/theorems/a88fcdc4-94ac-4e16-9ccc-5633f067b34f
-- title:
--   Assemble the bound over connected induced subgraphs
-- statement:
--   If every connected induced subgraph with at least three vertices satisfies the planar edge bound, then the whole graph satisfies it whenever the total vertex count is at least three, including when the graph is disconnected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_simple_edge_bound_components_bf226c5d
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hConnectedBounds : ∀ (S : Set V) [Fintype S],
      3 ≤ Fintype.card S →
      (G.induce S).Connected →
      (G.induce S).edgeSet.ncard + 6 ≤ 3 * Fintype.card S) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry
