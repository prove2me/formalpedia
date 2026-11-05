-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
-- name    : WilliamsonShmoys.finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:07:17.538426+00:00
-- url     : https://prove2.me/theorems/c1868ea9-2f79-4b93-ad6c-bc634ef3355f
-- title:
--   Finite local graph extensions yield a connected extension
-- statement:
--   For a finite ordered vertex type, if a graph property holds for an initial graph and every disconnected graph with the property admits a property-preserving extension by an edge between unreachable vertices, then there is a connected extension with the property and at least as many edges as the initial graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_local_extension_connected__p2m_92ab9f16_2d15_4356_b6df_90082235199d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ u v : V, ¬ G.Reachable u v ∧
        ∃ H : SimpleGraph V,
          P H ∧ G ≤ H ∧
          ∀ x y : V,
            H.Adj x y ↔
              G.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) :
    ∃ H : SimpleGraph V,
      P H ∧ H.Connected ∧ K.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
