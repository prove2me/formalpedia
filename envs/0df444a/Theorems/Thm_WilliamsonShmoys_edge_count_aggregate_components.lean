-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_aggregate_components
-- name    : WilliamsonShmoys.edge_count_aggregate_components
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:46:04.76374+00:00
-- url     : https://prove2.me/theorems/1716e745-d947-40c7-a5e9-082b625a8f02
-- title:
--   Aggregate connected induced edge bounds
-- statement:
--   If a finite family of vertex subsets has total cardinality equal to the graph's vertex count and its induced edge counts sum to the graph's edge count, and every subset induces a connected graph, then the stated bound for connected subsets of size at least three implies the bound for the whole graph, provided the graph has at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.edge_count_aggregate_components
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (C : Finset (Finset V))
    (hCard : 3 <= Fintype.card V)
    (hConnectedBounds :
      ∀ S : Finset V, 3 <= S.card → (L.induce S).Connected →
        ((L.induce S).edgeSet.ncard : Int) <= 3 * (S.card : Int) - 6)
    (hCardSum : ∑ S ∈ C, S.card = Fintype.card V)
    (hEdgeSum :
      (L.edgeSet.ncard : Int) = ∑ S ∈ C, ((L.induce S).edgeSet.ncard : Int))
    (hConnected : ∀ S ∈ C, (L.induce S).Connected) :
    (L.edgeSet.ncard : Int) <= 3 * (Fintype.card V : Int) - 6 := by sorry
