-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_eq_sum_induce
-- name    : WilliamsonShmoys.edge_ncard_eq_sum_induce
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:23:06.826132+00:00
-- url     : https://prove2.me/theorems/aef947e5-5d4b-47b3-a2ca-3577ac4b0ebb
-- title:
--   Count global edges by their unique partition block
-- statement:
--   The edge count of the graph is the sum of the edge counts induced by the blocks. Every edge is in a block by hadj, and disjointness ensures that two distinct blocks cannot both contain its endpoints. A proof can establish a bijection between global edges and the disjoint union of block-induced edges, then use finite cardinality accounting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_ncard_eq_sum_induce
    {V : Type} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ S, S ∈ C ∧ v ∈ S)
    (hdisjoint : ∀ S, S ∈ C → ∀ T, T ∈ C → S ≠ T → Disjoint S T)
    (hadj : ∀ ⦃u v : V⦄, G.Adj u v → ∃ S, S ∈ C ∧ u ∈ S ∧ v ∈ S) :
    G.edgeSet.ncard = ∑ S ∈ C, (G.induce (↑S : Set V)).edgeSet.ncard := by sorry
