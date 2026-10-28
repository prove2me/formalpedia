-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_supergraph_from_one_step
-- name    : WilliamsonShmoys.finite_connected_supergraph_from_one_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T13:58:19.195276+00:00
-- url     : https://prove2.me/theorems/2a3caaec-ed56-4a82-ae39-b374402ef517
-- title:
--   Finite connected supergraph from a strict one-step extension
-- statement:
--   For a finite ordered vertex type, if every disconnected P-supergraph of W admits a strict P-supergraph, then W has a connected P-supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

theorem WilliamsonShmoys.finite_connected_supergraph_from_one_step
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P W)
    (hStep : ∀ G : SimpleGraph V, W ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ G ≠ K ∧ P K) :
    ∃ H : SimpleGraph V, W ≤ H ∧ H.Connected ∧ P H := by sorry
