-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_augmentation_from_one_step
-- name    : WilliamsonShmoys.finite_graph_augmentation_from_one_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T09:54:33.299585+00:00
-- url     : https://prove2.me/theorems/8ce53f59-422b-4918-b7fa-a9138f896327
-- title:
--   Finite graph augmentation from a strict one-step extension
-- statement:
--   If a finite graph has property P and every disconnected P supergraph has a strict P extension, then it has a connected P supergraph with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_augmentation_from_one_step
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hStep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ G ≠ K ∧ P K) :
    ∃ H : SimpleGraph V,
      W ≤ H ∧ H.Connected ∧ P H ∧ W.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
