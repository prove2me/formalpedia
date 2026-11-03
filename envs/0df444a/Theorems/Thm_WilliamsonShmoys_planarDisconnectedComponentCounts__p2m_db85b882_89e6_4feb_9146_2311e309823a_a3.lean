-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
-- name    : WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:26:20.493799+00:00
-- url     : https://prove2.me/theorems/d29cc926-0e2e-4704-bc36-256caa004206
-- title:
--   Componentwise edge counts for a disconnected planar graph with at least three vertices
-- statement:
--   For a disconnected finite planar graph with at least three vertices, there is a partition into at least two nonempty, pairwise disjoint blocks covering all vertices. The block sizes sum to the vertex count, their internal edge counts sum to the graph’s edge count, and each block’s edge count plus three is at most three times its size. The size hypothesis excludes the empty-graph obstruction in the earlier child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDisconnectedComponentCounts__p2m_db85b882_89e6_4feb_9146_2311e309823a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : HasPlanarDrawingOn L)
    (hconn : ¬ L.Connected)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (C : Finset (Finset V)) (edgeCount : Finset V → Nat),
      2 ≤ C.card ∧
      (∀ s ∈ C, s.Nonempty) ∧
      (∀ v : V, ∃ s ∈ C, v ∈ s) ∧
      (∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t) ∧
      (∑ s ∈ C, s.card) = Fintype.card V ∧
      (∑ s ∈ C, edgeCount s) = (letI : DecidableRel L.Adj := dL; L.edgeFinset.card) ∧
      (∀ s ∈ C, edgeCount s + 3 ≤ 3 * s.card) := by sorry
