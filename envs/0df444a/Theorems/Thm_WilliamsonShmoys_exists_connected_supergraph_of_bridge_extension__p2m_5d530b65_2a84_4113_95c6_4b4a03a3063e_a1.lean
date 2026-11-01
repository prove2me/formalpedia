-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1
-- name    : WilliamsonShmoys.exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:54:40.126207+00:00
-- url     : https://prove2.me/theorems/1743449e-70b2-453d-82e4-df1f7d1e75bd
-- title:
--   Finite iteration of bridge extensions
-- statement:
--   For a finite vertex type, any property that holds for an initial graph and can be preserved while adding a bridge between unreachable vertices whenever the current supergraph is disconnected yields a connected supergraph with that property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_supergraph_of_bridge_extension__p2m_5d530b65_2a84_4113_95c6_4b4a03a3063e_a1
    {V : Type} [Fintype V] [DecidableEq V]
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
