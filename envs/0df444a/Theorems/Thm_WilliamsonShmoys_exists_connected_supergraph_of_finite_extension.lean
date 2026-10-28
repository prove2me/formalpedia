-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_finite_extension
-- name    : WilliamsonShmoys.exists_connected_supergraph_of_finite_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:26:30.808994+00:00
-- url     : https://prove2.me/theorems/06b7fdc0-f509-4865-8946-cf9394fbc43b
-- title:
--   A finite edge-extension property yields a connected supergraph
-- statement:
--   For a finite vertex type, if a graph has property P and every disconnected P-supergraph of it admits a strict edge extension still having P, then it has a connected P-supergraph. Prove this by maximizing the number of edges among P-supergraphs; the extension hypothesis rules out a disconnected maximizer. The argument also handles the empty vertex type, where the starting graph is already connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_connected_supergraph_of_finite_extension
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H)
    (hstep : ∀ G : SimpleGraph V,
      H.edgeSet ⊆ G.edgeSet →
      P G →
      ¬ G.Connected →
      ∃ K : SimpleGraph V, G.edgeSet ⊂ K.edgeSet ∧ P K) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧ K.Connected ∧ P K := by sorry
