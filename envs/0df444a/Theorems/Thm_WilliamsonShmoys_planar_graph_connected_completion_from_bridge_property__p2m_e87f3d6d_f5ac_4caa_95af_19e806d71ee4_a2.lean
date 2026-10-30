-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- name    : WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:15.29585+00:00
-- url     : https://prove2.me/theorems/39b2e6d4-604e-4f41-9365-8bd67e4be3f2
-- title:
--   Iterate a property-preserving bridge extension
-- statement:
--   For any predicate on finite graphs, if it holds initially and every pair of unreachable vertices can be joined by adding exactly their edge while preserving the predicate, then there is a connected supergraph satisfying the predicate. This removes the repeated component-selection and termination argument from the parent. A proof route inducts on the finite number of reachability classes: when the graph is not connected, select vertices from distinct classes, apply the bridge hypothesis, and use the strict decrease in class count. Nonemptiness covers the zero-vertex boundary case. The remaining core obligation is this finite graph induction; the geometric content is isolated in the bridge child.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_connected_completion_from_bridge_property__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P M)
    (hne : Nonempty V)
    (hbridge : ∀ (G : SimpleGraph V), P G →
      ∀ x y : V, ¬ G.Reachable x y →
        ∃ N : SimpleGraph V,
          G ≤ N ∧
          (∀ u v, N.Adj u v ↔
            G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
          P N) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ (∀ x y, N.Reachable x y) ∧ P N := by
  sorry
