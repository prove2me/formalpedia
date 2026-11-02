-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- name    : WilliamsonShmoys.planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:43:43.871847+00:00
-- url     : https://prove2.me/theorems/313ad367-69f9-46a6-a8a9-ceaec7db9c1a
-- title:
--   Connected-component partition and edge conservation
-- statement:
--   A finite disconnected graph with at least three vertices admits a partition into at least two nonempty connected induced subgraphs. The blocks cover the vertices and are pairwise disjoint; their sizes sum to the order of the graph, and their induced edge counts sum to the total edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planarDisconnectedComponentPartitionCounts__p2m_d29cc926_0e2e_4704_bc36_256caa004206_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    letI : DecidableRel L.Adj := dL
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = L.edgeFinset.card ∧
      (∀ s ∈ C, (L.induce (↑s : Set V)).Connected) ∧
      (∀ s ∈ C, edgeCount s = (L.induce (↑s : Set V)).edgeFinset.card) := by sorry
