-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_completion_from_steps__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a4
-- name    : WilliamsonShmoys.finite_graph_completion_from_steps__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:05:19.195528+00:00
-- url     : https://prove2.me/theorems/a8bea31e-3783-4d2f-854a-f12bba311eb2
-- title:
--   Terminate finite edge-extension steps at a connected graph
-- statement:
--   On a finite vertex type, if every disconnected intermediate supergraph satisfying an invariant can be extended while preserving that invariant and strictly adding an edge, then there is a connected extension satisfying the invariant and the required edge condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_completion_from_steps__p2m_0ac1f81c_3fb8_44a1_92c7_855048ff841d_a4
    {V : Type} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (P : SimpleGraph V → Prop)
    (hP : P K)
    (step : ∀ G : SimpleGraph V,
      K ≤ G →
      (∀ x y : V, G.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y) →
      P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ P H ∧
        (∀ x y : V, H.Adj x y → G.Adj x y ∨ ¬ K.Reachable x y) ∧
        ∃ u v : V, ¬ G.Adj u v ∧ H.Adj u v)
    (hNotConnected : ¬ K.Connected) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ P H ∧ H.Connected ∧
      ∀ x y : V, H.Adj x y → K.Adj x y ∨ ¬ K.Reachable x y := by sorry
