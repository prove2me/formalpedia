-- Prove2me | Theorems.Thm_WilliamsonShmoys_iterate_edge_extensions__p2m_8875bb45_86a4_4d7c_b2ea_8d56d84fd5c3_a1
-- name    : WilliamsonShmoys.iterate_edge_extensions__p2m_8875bb45_86a4_4d7c_b2ea_8d56d84fd5c3_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:15:24.258622+00:00
-- url     : https://prove2.me/theorems/99c4ffa4-e8f8-4690-8e77-fae2afbeca57
-- title:
--   Iterate finite graph edge extensions while preserving a property
-- statement:
--   For a finite vertex type, if a graph property is preserved by an edge-addition step that joins two distinct, nonadjacent, unreachable vertices whenever the current graph is disconnected, then any graph satisfying the property has a connected supergraph that also satisfies it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.iterate_edge_extensions__p2m_8875bb45_86a4_4d7c_b2ea_8d56d84fd5c3_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V)
    (hK : P K)
    (hStep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ u v : V,
        u ≠ v ∧ ¬ G.Reachable u v ∧ ¬ G.Adj u v ∧
        P (G ⊔ SimpleGraph.fromRel (fun x y : V => x = u ∧ y = v)))
    (hDisconnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ H.Connected ∧ P H := by sorry
