-- Prove2me | Theorems.Thm_finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
-- name    : finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:40:28.432512+00:00
-- url     : https://prove2.me/theorems/59758877-c28f-4756-a5bc-fc8ad3e95fc8
-- title:
--   Finite graph bridge extension yields connectedness on nontrivial vertex types
-- statement:
--   On a finite vertex type with at least two vertices, if every graph satisfying P can be extended to a P graph with a crossing edge across any nontrivial cut that currently has no crossing edges, then every P graph has a P-preserving connected supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem finite_graph_bridge_extension_connected__p2m_be2db1e0_df49_4de2_8924_46bf2933b6cf_a2
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (K : SimpleGraph V) (hK : P K)
    (hcard : 2 ≤ Fintype.card V)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ (A : Set V), A.Nonempty → Aᶜ.Nonempty →
        (∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v) →
        ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
          ∃ u v, u ∈ A ∧ v ∉ A ∧ H.Adj u v) :
    ∃ H : SimpleGraph V, K ≤ H ∧ P H ∧ H.Connected := by sorry
