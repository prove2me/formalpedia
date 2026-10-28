-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_from_connected_induced_bounds_282b0fbb
-- name    : WilliamsonShmoys.edge_count_from_connected_induced_bounds_282b0fbb
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:16:18.252577+00:00
-- url     : https://prove2.me/theorems/1cb97b77-522a-4703-984d-ebd572644f48
-- title:
--   Assemble edge bounds over connected components
-- statement:
--   If every connected induced subgraph of at least three vertices satisfies the planar edge bound, then the whole finite simple graph with at least three vertices satisfies it. Decompose the graph into connected components, use the hypothesis on components of size at least three, bound components of sizes one and two directly, and sum the component inequalities.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_from_connected_induced_bounds_282b0fbb
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hConnectedBounds :
      ∀ S : Finset V, 3 <= S.card → (L.induce S).Connected →
        ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
