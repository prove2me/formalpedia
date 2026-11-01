-- Prove2me | Theorems.Thm_disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- name    : disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:56.608437+00:00
-- url     : https://prove2.me/theorems/c7083857-df92-4f70-92d2-0df298dc9395
-- title:
--   A disconnected graph has an edge-free nontrivial cut
-- statement:
--   If a finite graph is disconnected, some nonempty proper vertex set has no adjacency crossing from it to its complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem disconnected_graph_has_cut__p2m_59758877_c28f_4756_a5bc_fc8ad3e95fc8_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : ¬ G.Connected) :
    ∃ A : Set V, A.Nonempty ∧ Aᶜ.Nonempty ∧
      ∀ u ∈ A, ∀ v ∉ A, ¬ G.Adj u v := by sorry
