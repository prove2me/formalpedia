-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- name    : WilliamsonShmoys.finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:38:18.586705+00:00
-- url     : https://prove2.me/theorems/ae139772-cde8-4644-bb54-63943db19887
-- title:
--   Finite iteration of strict edge extensions
-- statement:
--   For a finite vertex type, if every disconnected graph satisfying an invariant can be extended to a graph satisfying the invariant by adding an edge between previously unreachable vertices, then every graph satisfying the invariant has a connected extension satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_connected_extension_of_local_step__p2m_343e7634_bf89_4d0d_a54b_557d3af37c62_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (step : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∀ (G : SimpleGraph V), P G →
      ∃ H : SimpleGraph V, G ≤ H ∧ H.Connected ∧ P H := by sorry
