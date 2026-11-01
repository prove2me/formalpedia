-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_iteration__p2m_890a21e4_ea5b_4fa2_834e_277ff81160e9_a1
-- name    : WilliamsonShmoys.finite_graph_extension_iteration__p2m_890a21e4_ea5b_4fa2_834e_277ff81160e9_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:18.905192+00:00
-- url     : https://prove2.me/theorems/4c711e56-a266-4982-b582-d72638742b9c
-- title:
--   Finite iteration of strict graph extensions
-- statement:
--   For a finite vertex type, if every disconnected graph extending G and satisfying P can be extended to another graph satisfying P by adding at least the old edges and an edge between two previously unreachable vertices, then a connected graph satisfying P contains all the edges of G.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_iteration__p2m_890a21e4_ea5b_4fa2_834e_277ff81160e9_a1
    {V : Type} [Fintype V]
    (G : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P G)
    (hstep : ∀ (K : SimpleGraph V),
      G.edgeSet ⊆ K.edgeSet →
      P K →
      ¬ K.Connected →
      ∃ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet ∧
        (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
        P L) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧ H.Connected ∧ P H := by sorry
