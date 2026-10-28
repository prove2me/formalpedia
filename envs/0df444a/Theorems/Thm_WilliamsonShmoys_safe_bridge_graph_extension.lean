-- Prove2me | Theorems.Thm_WilliamsonShmoys_safe_bridge_graph_extension
-- name    : WilliamsonShmoys.safe_bridge_graph_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T11:31:48.484075+00:00
-- url     : https://prove2.me/theorems/419667a8-9c9f-44f6-8b7c-4f28e62be14d
-- title:
--   Add a safe bridge pair to the graph
-- statement:
--   Given a safe bridge, construct a simple graph containing G whose edges are either old G edges or pairs not reachable in G, and exhibit a newly added edge between non-reachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_HasSafeBridge
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.safe_bridge_graph_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (p : V → ℝ × ℝ)
    (arc : V → V → ℝ → ℝ × ℝ)
    (hBridge : WilliamsonShmoys.HasSafeBridge G p arc) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      (∀ u v, H.Adj u v → G.Adj u v ∨ ¬ G.Reachable u v) ∧
      ∃ u v, H.Adj u v ∧ ¬ G.Reachable u v := by sorry
