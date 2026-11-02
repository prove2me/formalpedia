-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- name    : WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T08:10:28.994202+00:00
-- url     : https://prove2.me/theorems/7f486b2e-cbf8-4188-b8c7-745bb19596ec
-- title:
--   Componentwise edge counts for a disconnected planar graph
-- statement:
--   A disconnected graph with a crossing-free drawing can be partitioned into at least two nonempty vertex blocks. The blocks cover the vertices and are pairwise disjoint; their sizes and internal edge counts sum to the graph totals. Each block has at most three times its size minus three internal edges. To prove this, take connected components, restrict the drawing to each, apply the connected planar Euler bound for blocks of size at least three, and check sizes one and two directly. This isolates the planar component estimate, which is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected) :
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ∧
      (∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card) := by sorry
