-- Prove2me | Theorems.Thm_finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a1
-- name    : finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:22:16.955589+00:00
-- url     : https://prove2.me/theorems/d02280d8-d659-426e-a337-40df26331851
-- title:
--   Finite graph bridge extension yields connectedness
-- statement:
--   For a finite graph property P, if every graph satisfying P can be extended to another graph satisfying P by adding an edge across every nontrivial edge-free cut, then every graph satisfying P has a P-preserving supergraph that is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ (A : Set V), A.Nonempty → Aᶜ.Nonempty →
        (∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) →
        ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
          ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ H.Connected := by sorry
